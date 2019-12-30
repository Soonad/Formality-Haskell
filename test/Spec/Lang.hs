module Spec.Lang where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Core
import Lang

eval' :: Parser a -> Text -> Maybe a
eval' p s =
  let res = runParserT (runStateT p (Ctx [] 0)) "" s in
  case res of
    Identity (Left e)       -> Nothing
    Identity (Right (a, b)) -> Just a

spec :: SpecWith ()
spec = do
  describe "Names" $ do
    it "initial letter or underscores _a" $ do
      eval' name "a" `shouldBe` (Just "a")
      eval' name "_a" `shouldBe` (Just "_a")
    it "initial underscores allow for post-initial number: _1" $ do
      eval' name "_1" `shouldBe` (Just "_1")
    it "initial number fails : 1" $ do
      eval' name "1" `shouldBe` Nothing
    it "names with only symbols should fail: __" $ do
      eval' name "_" `shouldBe` Nothing
      eval' name "__" `shouldBe` Nothing
      eval' name "_." `shouldBe` Nothing
    it "symbols following initial letter okay: a_" $ do
      eval' name "a_" `shouldBe` (Just "a_")
      eval' name "a_." `shouldBe` (Just "a_.")

  describe "Forall/Lambdas" $ do
    it "basic syntax: (A : Type) => A" $ do
      eval' allLam "(A : Type) => A" `shouldBe` (Just $ Lam "A" Typ (Var 0) False)
      eval' allLam "(A : Type) -> A" `shouldBe` (Just $ All "A" Typ (Var 0) False)

    it "erased arguments: (A : Type;) => A" $ do
      eval' allLam "(A : Type;) => A" `shouldBe` (Just $ Lam "A" Typ (Var 0) True)
      eval' allLam "(A : Type;) -> A" `shouldBe` (Just $ All "A" Typ (Var 0) True)

    it "multiple arguments: (A : Type, B : Type) => A" $ do
      eval' allLam "(A : Type, B : Type) => A" `shouldBe`
        (Just $ (Lam "A" Typ (Lam "B" Typ (Var 1) False) False))
      eval' allLam "(A : Type, B : Type, C : Type) => A" `shouldBe`
        (Just $ (Lam "A" Typ (Lam "B" Typ (Lam "C" Typ (Var 2) False) False) False))

    it "holes for argument type: (A) => A" $ do
      eval' allLam "(A) => A" `shouldBe` (Just $ Lam "A" (Hol "#0") (Var 0) False)
      eval' allLam "(A,B) => A" `shouldBe`
        (Just $ (Lam "A" (Hol "#0") (Lam "B" (Hol "#1") (Var 1) False) False))

    it "anonymous arguments: (:Type) -> A" $ do
      eval' allLam "(:Type) -> A" `shouldBe` (Just $ All "_" Typ (Ref "A") False)
      eval' allLam "(:Type, :Type) -> A" `shouldBe` 
        (Just $ All "_" Typ (All "_" Typ (Ref "A") False) False)

    it "correct deBruijn indices" $ do
      eval' allLam "(A : Type, x : A) -> A" `shouldBe` 
        (Just $ (All "A" Typ (All "x" (Var 0) (Var 1) False) False))
      eval' allLam "(A : Type, B : Type, x : A) -> A" `shouldBe` 
        (Just $ (All "A" Typ (All "B" Typ (All "x" (Var 1) (Var 2) False) False) False))

  describe "Application" $ do
    it "function style applications: f(a)" $ do
      eval' expr "f(a)" `shouldBe` (Just (App (Ref "f") (Ref "a") False))
    it "multiple arguments: f(a,b,c)" $ do
      eval' expr "f(a,b)" `shouldBe` 
        (Just (App (App (Ref "f") (Ref "a") False) (Ref "b") False))
      eval' expr "f(a,b,c)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") False) (Ref "b") False) (Ref "c") False))
    it "parenthesized arguments: f(a)(b)(c)" $ do
      eval' expr "f(a)(b)(c)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") False) (Ref "b") False) (Ref "c") False))
    it "erased parenthesized arguments: f(a;)(b;)(c;)" $ do
      eval' expr "f(a;)(b;)(c;)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") True) (Ref "b") True) (Ref "c") True))
    it "erased arguments: f(a;b;c;)" $ do
      eval' expr "f(a;b;c;)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") True) (Ref "b") True) (Ref "c") True))
    it "applying a lambda: ((x) => x)(a,b)" $ do
      eval' expr "((x) => x)(a,b)" `shouldBe` 
        (Just (App (App (Lam "x" (Hol "#0") (Var 0) False) (Ref "a") False) (Ref "b") False))
    it "lambda style applications: (f a b c)" $ do
      eval' expr "(f a b c)" `shouldBe`
        (Just (App (App (App (Ref "f") (Ref "a") False) (Ref "b") False) (Ref "c") False))
    it "lambda style applications: (f (a b) c)" $ do
      eval' expr "(f (a b) c)" `shouldBe`
        (Just (App (App (Ref "f") (App (Ref "a") (Ref "b") False) False) (Ref "c") False))
      eval' expr "(f (a (b c)))" `shouldBe`
        (Just (App (Ref "f") (App (Ref "a") (App (Ref "b") (Ref "c") False) False) False))

--  describe "Def" $ do

