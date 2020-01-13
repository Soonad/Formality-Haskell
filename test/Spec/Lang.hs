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
import           Control.Monad.RWS.Lazy    hiding (All)

import Core
import Lang

parse' :: Parser a -> Text -> Maybe a
parse' p s =
  let res = runParserT (runRWST p (ParseEnv []) (ParseState 0)) "" s in
  case res of
    Identity (Left e)       -> Nothing
    Identity (Right (a, st, w)) -> Just a

spec :: SpecWith ()
spec = do
  describe "Names" $ do
    it "initial letter or underscores: \"_a\"" $ do
      parse' name "a" `shouldBe` (Just "a")
      parse' name "_a" `shouldBe` (Just "_a")
    it "initial underscores allow for post-initial number: \"_1\"" $ do
      parse' name "_1" `shouldBe` (Just "_1")
    it "initial number fails : \"1\"" $ do
      parse' name "1" `shouldBe` Nothing
    it "names with only symbols should fail: \"__\"" $ do
      parse' name "_" `shouldBe` Nothing
      parse' name "__" `shouldBe` Nothing
      parse' name "_." `shouldBe` Nothing
    it "symbols following initial letter okay: \"a_\"" $ do
      parse' name "a_" `shouldBe` (Just "a_")
      parse' name "a_." `shouldBe` (Just "a_.")

  describe "Forall/Lambdas" $ do
    it "basic syntax: \"(A : Type) => A\"" $ do
      parse' allLam "(A : Type) => A" `shouldBe` (Just $ Lam "A" Typ Keep (Var 0))
      parse' allLam "(A : Type) -> A" `shouldBe` (Just $ All "A" Typ Keep (Var 0))

    it "erased arguments: \"(A : Type;) => A\"" $ do
      parse' allLam "(A : Type;) => A" `shouldBe` (Just $ Lam "A" Typ Eras (Var 0))
      parse' allLam "(A : Type;) -> A" `shouldBe` (Just $ All "A" Typ Eras (Var 0))

    it "multiple arguments: \"(A : Type, B : Type) => A\"" $ do
      parse' allLam "(A : Type, B : Type) => A" `shouldBe`
        (Just $ (Lam "A" Typ Keep (Lam "B" Typ Keep (Var 1))))
      parse' allLam "(A : Type, B : Type, C : Type) => A" `shouldBe`
        (Just $ (Lam "A" Typ Keep (Lam "B" Typ Keep (Lam "C" Typ Keep (Var 2)))))

    it "holes for argument type: \"(A) => A\"" $ do
      parse' allLam "(A) => A" `shouldBe` (Just $ Lam "A" (Hol "#0") Keep (Var 0))
      parse' allLam "(A,B) => A" `shouldBe`
        (Just $ (Lam "A" (Hol "#0") Keep (Lam "B" (Hol "#1") Keep (Var 1))))

    it "anonymous arguments: \"(:Type) -> A\"" $ do
      parse' allLam "(:Type) -> A" `shouldBe` (Just $ All "_" Typ Keep (Ref "A"))
      parse' allLam "(:Type, :Type) -> A" `shouldBe` 
        (Just $ All "_" Typ Keep (All "_" Typ Keep (Ref "A")))

    it "correct deBruijn indices" $ do
      parse' allLam "(A : Type, x : A) -> A" `shouldBe` 
        (Just $ (All "A" Typ Keep (All "x" (Var 0) Keep (Var 1))))
      parse' allLam "(A : Type, B : Type, x : A) -> A" `shouldBe` 
        (Just $ (All "A" Typ Keep (All "B" Typ Keep (All "x" (Var 1) Keep (Var 2)))))

  describe "Application" $ do
    it "function style applications: \"f(a)\"" $ do
      parse' expr "f(a)" `shouldBe` (Just (App (Ref "f") (Ref "a") Keep))
    it "multiple arguments: \"f(a,b,c)\"" $ do
      parse' expr "f(a,b)" `shouldBe` 
        (Just (App (App (Ref "f") (Ref "a") Keep) (Ref "b") Keep))
      parse' expr "f(a,b,c)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") Keep) (Ref "b") Keep) (Ref "c") Keep))
    it "parenthesized arguments: \"f(a)(b)(c)\"" $ do
      parse' expr "f(a)(b)(c)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") Keep) (Ref "b") Keep) (Ref "c") Keep))
    it "erased parenthesized arguments: \"f(a;)(b;)(c;)\"" $ do
      parse' expr "f(a;)(b;)(c;)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") Eras) (Ref "b") Eras) (Ref "c") Eras))
    it "erased arguments: \"f(a;b;c;)\"" $ do
      parse' expr "f(a;b;c;)" `shouldBe` 
        (Just (App (App (App (Ref "f") (Ref "a") Eras) (Ref "b") Eras) (Ref "c") Eras))
    it "applying a lambda: \"((x) => x)(a,b)\"" $ do
      parse' expr "((x) => x)(a,b)" `shouldBe` 
        (Just (App (App (Lam "x" (Hol "#0") Keep (Var 0)) (Ref "a") Keep) (Ref "b") Keep))
    it "lambda style applications: \"(f a b c)\"" $ do
      parse' expr "(f a b c)" `shouldBe`
        (Just (App (App (App (Ref "f") (Ref "a") Keep) (Ref "b") Keep) (Ref "c") Keep))
    it "lambda style applications: \"(f (a b) c)\"" $ do
      parse' expr "(f (a b) c)" `shouldBe`
        (Just (App (App (Ref "f") (App (Ref "a") (Ref "b") Keep) Keep) (Ref "c") Keep))
      parse' expr "(f (a (b c)))" `shouldBe`
        (Just (App (Ref "f") (App (Ref "a") (App (Ref "b") (Ref "c") Keep) Keep) Keep))

  describe "Def" $ do
    it "bare-style definitions: \"a 1\"" $ do
      parse' def "a 1" `shouldBe` (Just ("a",Val 1))
    it "equals-style definitions: \"a = 1\"" $ do
      parse' def "a = 1" `shouldBe` (Just ("a",Val 1))
    it "definitions with arguments: \"a(x) 1\"" $ do
      parse' def "a(x) 1" `shouldBe` (Just ("a",Lam "x" (Hol "#0") Keep (Val 1)))
    it "equals-style definitions with arguments: \"a(x) = 1\"" $ do
      parse' def "a(x) = 1" `shouldBe` (Just ("a",Lam "x" (Hol "#0") Keep (Val 1)))
    it "definitions with types: \"a : Number 1\"" $ do
      parse' def "a : Number 1" `shouldBe` (Just ("a",Ann Num (Val 1)))
    it "definitions with types: \"a : Number = 1\"" $ do
      parse' def "a : Number = 1" `shouldBe` (Just ("a",Ann Num (Val 1)))

