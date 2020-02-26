module Spec.Parser.PreModule where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Core                       (Eras (..), Name, Op (..))
import           Lang

import           Parser.PreModule

import           Spec.Parser.Utils

spec :: SpecWith ()
spec = do
  describe "Def" $ do
    it "bare-style definitions: \"a 1\"" $ do
      parse' definition "a 1" `shouldBe` (Just $ Expr "a" (Val 1))
    it "semicolon-style definitions: \"a; 1\"" $ do
      parse' definition "a; 1" `shouldBe` (Just $ Expr "a" (Val 1))
    it "definitions with arguments: \"a(x) 1\"" $ do
      parse' definition "a(x) 1" `shouldBe` (Just $ Expr "a" (Lam "x" (Hol "#0") Keep (Val 1)))
    it "definitions with arguments: \"a(x) x\"" $ do
      parse' definition "a(x) x" `shouldBe` (Just $ Expr "a" (Lam "x" (Hol "#0") Keep (Var 0)))
    it "definitions with arguments (semicolon): \"a(x); 1\"" $ do
      parse' definition "a(x); 1" `shouldBe` (Just $ Expr "a"(Lam "x" (Hol "#0") Keep (Val 1)))
    it "definitions with types: \"a : Number 1\"" $ do
      parse' definition "a : Number 1" `shouldBe` (Just $ Expr "a" (Ann Num (Val 1)))
    it "definitions with types (semicolon): \"a : Number; 1\"" $ do
      parse' definition "a : Number; 1" `shouldBe` (Just $ Expr "a" (Ann Num (Val 1)))
    it "definitions with arguments and types: \"a(A : Type, x : A) : A; x\"" $ do
      parse' definition "a(A : Type, x : A) : A; x" `shouldBe`
        (Just $ Expr "a" (Ann (All "A" Typ Keep (All "x" (Var 0) Keep (Var 1)))
                             (Lam "A" Typ Keep (Lam "x" (Var 0) Keep (Var 0)))))

  describe "ADT" $ do
    it "T Empty" $ do
        parse' datatype "T Empty" `shouldBe` (Just $ Data "Empty" [] [] [])
    it "T Bool | true | false" $ do
        parse' datatype "T Bool | true | false" `shouldBe` 
          (Just $ Data "Bool" [] [] [Ctor "true" [] Nothing, Ctor "false" [] Nothing])
    it "T The{A} (x : A) | the(x : A) : The(A,x)" $ do
        parse' datatype "T The{A} (x : A) | the(x : A) : The(A,x)" `shouldBe`
          (Just $ 
            Data "The" [("A", Hol "#0")] [("x", Var 0)] 
              [Ctor "the" [("x", Var 0)]
                (Just (App (App (Ref "The" 0) (Var 1) Keep) (Var 0) Keep))])
    it "T Either{A,B} | lft(value : A) | rgt(value : B)" $ do
       parse' datatype "T Either{A,B} | lft(value : A) | rgt(value : B)" `shouldBe`
         (Just $
           Data "Either" [("A", Hol "#0"), ("B",Hol "#1")] []
             [ Ctor "lft" [("value", Var 1)] Nothing
             , Ctor "rgt" [("value", Var 0)] Nothing
             ]
         )

  describe "Enum" $ do
    it "enum | FOO | BAR" $ do
      parse' enum "enum | FOO | BAR" `shouldBe` (Just $ Enum ["FOO", "BAR"])

  describe "import" $ do
    it "import Nat" $ do
      parse' import_ "import Nat" `shouldBe` (Just $ Impt "Nat" "")
