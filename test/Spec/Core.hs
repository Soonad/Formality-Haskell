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

      it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isEven(42)\"" $ do
        eval' "f"
          (T.concat
            [ "f let ("
            , "    isOdd(x)  = if x === 1 then 1 else isEven(x - 1);"
            , "    isEven(x) = if x === 1 then 0 else isOdd(x - 1);"
            , "  );"
            , "isEven(42)"
            ]) `shouldBe`
          (Right $ U64 1)

      it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isOdd(43)\"" $ do
        eval' "f"
          (T.concat
            [ "f let ("
            , "    isOdd(x) = if x === 1 then 1 else isEven(x - 1); "
            , "    isEven(x) = if x === 1 then 0 else isOdd(x - 1);"
            , "   );"
            , "isOdd(43)"
            ]) `shouldBe`
          (Right $ U64 1)
