{-# LANGUAGE QuasiQuotes #-}

module Spec.Core where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Data.Void
import           Data.Maybe
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import qualified Data.Map.Strict as M
import           Data.Set               (Set)
import qualified Data.Set               as Set

import           Text.Megaparsec            hiding (State)
import           Text.RawString.QQ

import qualified Data.Text              as T
import qualified Data.Text.IO           as TIO

import Core
import Lang hiding (Term(..))
import CoreSyn hiding (_terms)
import Parser hiding (Term(..))

data Err
  = ErrParse (ParseErrorBundle Text Void)
  | ErrSyn SynError
  | ErrEval
  deriving (Eq,Show)

parse' :: Show a => Parser a -> Text -> Either Err (a, ParseState)
parse' p s = let
  l = Left . ErrParse
  r = \(a, st, w) -> Right (a,st)
  in either l r (parseDefault p s)

-- core synthesis test
syn' :: Text -> Either Err Core.Module
syn' txt = do
  (ds, ParseState _ ns _) <- parse' premodule txt
  let env = SynEnv $ M.fromList $ (\x -> (x,[x])) <$> (Set.toList ns)
  let ste = SynState 0 M.empty
  either (Left . ErrSyn) Right $ coreSyn env ste ds

eval' :: Name -> Text -> Either Err Term
eval' name txt = do
  modl <- syn' txt
  term  <- maybe (Left ErrEval) Right $ M.lookup name (_defs modl)
  return $ eval term modl


synFile:: FilePath -> IO ()
synFile f = do
  txt <- TIO.readFile f
  print $ syn' txt

evalFile:: FilePath -> IO ()
evalFile f = do
  txt <- TIO.readFile f
  prettyModule $ syn' txt
  print $ eval' "main" txt

debug_evalFile:: FilePath -> IO Term
debug_evalFile f = do
  txt <- TIO.readFile f
  let s = syn' txt
  prettyModule $ s
  a <- either (\x -> print x >> error "Error") return s
  term  <- maybe (error "Error") return $ M.lookup "main" (_defs a)
  debug_eval term a


prettyModule :: Either Err Core.Module -> IO ()
prettyModule (Left e) = print e
prettyModule (Right (Module m)) = go (M.toList m)
  where
    go ((n,t):ns) = putStr (T.unpack n) >> putStr " = " >> print t >> go ns
    go [] = putStrLn ""

spec :: SpecWith ()
spec = do
  describe "Application" $ do
    it "applying a lambda: \"((x) => x)(1) ~> 1\"" $ do
      eval' "f" "f ((x) => x)(1)" `shouldBe` (Right $ U64 1)

  describe "References" $ do
    it "referencing a Let: \"let x = 0; x\"" $ do
      eval' "f" "f let x = 0; x" `shouldBe` (Right $ U64 0)
    it "name-shadowing with let: \"let x = 1; let x = 0; x\"" $ do
      eval' "f" "f let x = 1; let x = 0; x" `shouldBe` (Right $ U64 0)
    it "\"umbral\" referencing of shadowed names: \"let x = 1; let x = 0; ^x\"" $ do
      eval' "f" "f let x = 1; let x = 0; ^x" `shouldBe` (Right $ U64 1)
    it "CoreSyn Error: can't reference out of scope: \"let x = 1; let x = 0; ^^x\"" $ do
      eval' "f" "f let x = 1; let x = 0; ^^x"
        `shouldBe`
        (Left $ ErrSyn 
          (UndefinedReference "x" 2 0 
            (M.fromList [("f",["f"]), ("x", ["$x1","$x0"])])
          )
        )

    describe "mixing lets and lambdas" $ do
      it "\"let x = 2; let x = 1; ((x) => x)(0)\"" $ do
        eval' "f" "f let x = 2; let x = 1; ((x) => x)(0)"
          `shouldBe` (Right $ U64 0)
      it "\"let x = 2; let x = 1; ((x) => ^x)(0)\"" $ do
        eval' "f" "f let x = 2; let x = 1; ((x) => ^x)(0)"
          `shouldBe` (Right $ U64 1)
      it "\"let x = 2; let x = 1; ((x) => ^^x)(0)\"" $ do
        eval' "f" "f let x = 2; let x = 1; ((x) => ^^x)(0)"
          `shouldBe` (Right $ U64 2)

      it "\"let x = 2; let x = 1; ((x) => ^^^x)(0)\"" $ do
        eval' "f" "f let x = 2; let x = 1; ((x) => ^^^x)(0)"
          `shouldBe`
          (Left $ ErrSyn (UndefinedReference "x" 2 1
             (M.fromList [("f",["f"]), ("x",["$x1", "$x0"])]))
          )
      it "\"(x) => let x = 1; let x = 0; x)(2)\"" $ do
        eval' "f" "f ((x) => let x = 1; let x = 0; x)(2)" 
          `shouldBe` (Right $ U64 0)
      it "\"((x) => let x = 1; let x = 0; ^x)(2)\"" $ do
        eval' "f" "f ((x) => let x = 1; let x = 0; ^x)(2)"
          `shouldBe` (Right $ U64 1)
      it "\"((x) => let x = 1; let x = 0; ^^x)(2)\"" $ do
        eval' "f" "f ((x) => let x = 1; let x = 0; ^^x)(2)"
          `shouldBe` (Right $ U64 2)

      it "\"((x) => let x = 1; let x = 0; ^^^x)(2)\"" $ do
        eval' "f" "f ((x) => let x = 1; let x = 0; ^^^x)(2)"
          `shouldBe`
          (Left $ ErrSyn (UndefinedReference "x" 2 1
             (M.fromList [("f",["f"]), ("x",["$x1", "$x0"])]))
          )

    describe "let block" $ do
      it "\"let (x = 1; y = 2); x\"" $ do
        eval' "f" "f let (x = 1; y = 2); x" `shouldBe`
          (Right $ U64 1)
      it "\"let (x = 1; y = 2); let (x = 3; y = 4); ^x\"" $ do
        eval' "f" "f let (x = 1; y = 2); let (x = 3; y = 4); ^x" `shouldBe`
          (Right $ U64 1)
      it "\"let (f(x,y) = x; y = f(1,2)); y\"" $ do
        eval' "f" "f let (f(x,y) = x; y = f(1,2)); y" `shouldBe` 
          (Right $ U64 1)

      it "mutual recursion" $ do
        (eval' "f" [r|
f
  let (
    isOdd(x)  = if x === 1 then 1 else isEven(x - 1);
    isEven(x) = if x === 1 then 0 else isOdd(x - 1);
  );
  isEven(42)

        |]) `shouldBe` (Right $ U64 1)

        (eval' "f" [r|
f
  let (
    isOdd(x)  = if x === 1 then 1 else isEven(x - 1);
    isEven(x) = if x === 1 then 0 else isOdd(x - 1);
  );
  isOdd(43)

        |]) `shouldBe` (Right $ U64 1)

      it "closure" $ do
        (eval' "main" [r|
main f(1,2,3)

f(x,y,z)
  let p = x
  let q = y
  let r = z
  p + q + r
        |]) `shouldBe` (Right $ U64 6)


        (eval' "main" [r|
main f(1,2,3,4)

f(x,y,z)
  let q = (a) => x + y + a
  (w) => q(1) + g(x,y,z) + w

g(x,y,z)
  let p = x
  let q = y
  let r = z
  p + q + r
        |]) `shouldBe` (Right $ U64 14)

        (eval' "main" [r|
main f(1,2,3)

f(x,y,z)
  let q = y + z
  if x then q else y
        |]) `shouldBe` (Right $ U64 5)


