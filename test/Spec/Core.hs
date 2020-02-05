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

import           Text.Megaparsec            hiding (State)

import Core
import Lang hiding (Term(..))
import CoreSyn hiding (_terms)

data Err
  = ErrParse (ParseErrorBundle Text Void)
  | ErrSyn SynError
  | ErrEval
  deriving (Eq,Show)

parse' :: Show a => Parser a -> Text -> Either Err a
parse' p s = either (Left . ErrParse) (\(a, st, w) -> Right a) (parseDefault p s)


eval' :: Name -> Text -> Either Err Term
eval' name s = do
  defs <- parse' module_ s
  modl <- either (Left . ErrSyn) Right (coreSyn defs)
  idx  <- maybe (Left ErrEval) Right $ M.lookup name (_names modl)
  term <- maybe (Left ErrEval) Right $ M.lookup idx (_terms modl)
  return $ eval term modl

spec :: SpecWith ()
spec = do
  describe "Application" $ do
    it "applying a lambda: \"((x) => x)(1) ~> 1\"" $ do
      eval' "f" "f = ((x) => x)(1)" `shouldBe` (Right $ Val 1)

  describe "References" $ do
    it "bare reference: \"x\"" $ do
      eval' "f" "f = f" `shouldBe` (Right $ Ref "f" (ID 0))
    it "referencing a Let: \"let x = 0; x\"" $ do
      eval' "f" "f = let x = 0; x" `shouldBe` (Right $ Val 0)
    it "name-shadowing with let: \"let x = 1; let x = 0; x\"" $ do
      eval' "f" "f = let x = 1; let x = 0; x" `shouldBe` (Right $ Val 0)
    it "\"umbral\" referencing of shadowed names: \"let x = 1; let x = 0; ^x\"" $ do
      eval' "f" "f = let x = 1; let x = 0; ^x" `shouldBe` (Right $ Val 1)
    it "CoreSyn Error: can't reference out of scope: \"let x = 1; let x = 0; ^^x\"" $ do
      eval' "f" "f = let x = 1; let x = 0; ^^x" 
        `shouldBe`
        (Left $ ErrSyn (UndefinedReference "x" 2
           (M.fromList [("f",[ID 0]), ("x",[ID 2, ID 1])]))
        )

    describe "mixing lets and lambdas" $ do
      it "\"let x = 2; let x = 1; ((x) => x)(0)\"" $ do
        eval' "f" "f = let x = 2; let x = 1; ((x) => x)(0)" 
          `shouldBe` (Right $ Val 0)
      it "\"let x = 2; let x = 1; ((x) => ^x)(0)\"" $ do
        eval' "f" "f = let x = 2; let x = 1; ((x) => ^x)(0)" 
          `shouldBe` (Right $ Val 1)
      it "\"let x = 2; let x = 1; ((x) => ^^x)(0)\"" $ do
        eval' "f" "f = let x = 2; let x = 1; ((x) => ^^x)(0)" 
          `shouldBe` (Right $ Val 2)

      it "\"let x = 2; let x = 1; ((x) => ^^^x)(0)\"" $ do
        eval' "f" "f = let x = 2; let x = 1; ((x) => ^^^x)(0)"
          `shouldBe`
          (Left $ ErrSyn (UndefinedReference "x" 2
             (M.fromList [("f",[ID 0]), ("x",[ID 2, ID 1])]))
          )
      it "\"(x) => let x = 1; let x = 0; x)(2)\"" $ do
        eval' "f" "f = ((x) => let x = 1; let x = 0; x)(2)" 
          `shouldBe` (Right $ Val 0)
      it "\"((x) => let x = 1; let x = 0; ^x)(2)\"" $ do
        eval' "f" "f = ((x) => let x = 1; let x = 0; ^x)(2)"
          `shouldBe` (Right $ Val 1)
      it "\"((x) => let x = 1; let x = 0; ^^x)(2)\"" $ do
        eval' "f" "f = ((x) => let x = 1; let x = 0; ^^x)(2)"
          `shouldBe` (Right $ Val 2)

      it "\"((x) => let x = 1; let x = 0; ^^^x)(2)\"" $ do
        eval' "f" "f = ((x) => let x = 1; let x = 0; ^^^x)(2)"
          `shouldBe` 
          (Left $ ErrSyn (UndefinedReference "x" 2
             (M.fromList [("f",[ID 0]), ("x",[ID 2, ID 1])]))
          )

    describe "let block" $ do
      it "\"let (x = 1; y = 2); x\"" $ do
        eval' "f" "f = let (x = 1; y = 2); x" `shouldBe` (Right $ Val 1)
      it "\"let (x = 1; y = 2); let (x = 3; y = 4); ^x\"" $ do
        eval' "f" "f = let (x = 1; y = 2); let (x = 3; y = 4); ^x" `shouldBe`
          (Right $ Val 1)
      it "\"let (f(x,y) = x; y = f(1,2)); y\"" $ do
        eval' "f" "f = let (f(x,y) = x; y = f(1,2)); y" `shouldBe` (Right $ Val 1)

      it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isEven(42)\"" $ do
        eval' "f" "f = let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isEven(42)" `shouldBe` (Right $ Val 1)

      it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isOdd(43)\"" $ do
        eval' "f" "f = let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isOdd(43)" `shouldBe` (Right $ Val 1)

    --  it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isOdd(43)\"" $ do
    --    eval'
    --      (Let [ ("isOdd", Lam "x" (Hol "#0") Keep 
    --                  (Ite (Op2 EQL (Var 0) (Val 1)) (Val 1) 
    --                    (App (Ref "isEven" 0) (Op2 SUB (Var 0) (Val 1)) Keep)))
    --           , ("isEven", Lam "x" (Hol "#1") Keep 
    --                  (Ite (Op2 EQL (Var 0) (Val 1)) (Val 0) 
    --                    (App (Ref "isOdd" 0) (Op2 SUB (Var 0) (Val 1)) Keep)))
    --           ] (App (Ref "isOdd" 0) (Val 43) Keep)
    --       ) `shouldBe` (Val 1)
