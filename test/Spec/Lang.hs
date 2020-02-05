module Spec.Lang where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Control.Monad.RWS.Lazy    hiding (All)

import           Core (Eras (..), Name, Op (..))
import           Lang

parse' :: Show a => Parser a -> Text -> Maybe a
parse' p s = either (const Nothing) (\(a, st, w) -> Just a) (parseDefault p s)

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
    it "reserved words fail: \"let\", \"rewrite\"" $ do
      parse' name "let" `shouldBe` Nothing
      parse' name "rewrite" `shouldBe` Nothing

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
      parse' allLam "(:Type) -> A" `shouldBe` (Just $ All "_" Typ Keep (Ref "A" 0))
      parse' allLam "(:Type, :Type) -> A" `shouldBe` 
        (Just $ All "_" Typ Keep (All "_" Typ Keep (Ref "A" 0)))

    it "correct deBruijn indices" $ do
      parse' allLam "(A : Type, x : A) -> A" `shouldBe` 
        (Just $ (All "A" Typ Keep (All "x" (Var 0) Keep (Var 1))))
      parse' allLam "(A : Type, B : Type, x : A) -> A" `shouldBe` 
        (Just $ (All "A" Typ Keep (All "B" Typ Keep (All "x" (Var 1) Keep (Var 2)))))
      parse' allLam "(x : Number, Q : (y : Number) -> Type) -> Q(x)" `shouldBe`
        (Just $ All "x" Num Keep (All "Q" (All "y" Num Keep Typ) Keep (App (Var 0) (Var 1) Keep)))
      parse' allLam "(x : Number, Q : Number -> Type) -> Q(x)" `shouldBe` 
        (Just $ All "x" Num Keep (All "Q" (All "_" Num Keep Typ) Keep (App (Var 0) (Var 1) Keep)))

  describe "Application" $ do
    it "function style applications: \"f(a)\"" $ do
      parse' expr "f(a)" `shouldBe` (Just (App (Ref "f" 0) (Ref "a" 0) Keep))
    it "multiple arguments: \"f(a,b,c)\"" $ do
      parse' expr "f(a,b)" `shouldBe` 
        (Just (App (App (Ref "f" 0) (Ref "a" 0) Keep) (Ref "b" 0) Keep))
      parse' expr "f(a,b,c)" `shouldBe` 
        (Just (App (App (App (Ref "f" 0) (Ref "a" 0) Keep) (Ref "b" 0) Keep) (Ref "c" 0) Keep))
    it "parenthesized arguments: \"f(a)(b)(c)\"" $ do
      parse' expr "f(a)(b)(c)" `shouldBe` 
        (Just (App (App (App (Ref "f" 0) (Ref "a" 0) Keep) (Ref "b" 0) Keep) (Ref "c" 0) Keep))
    it "erased parenthesized arguments: \"f(a;)(b;)(c;)\"" $ do
      parse' expr "f(a;)(b;)(c;)" `shouldBe` 
        (Just (App (App (App (Ref "f" 0) (Ref "a" 0) Eras) (Ref "b" 0) Eras) (Ref "c" 0) Eras))
    it "erased arguments: \"f(a;b;c;)\"" $ do
      parse' expr "f(a;b;c;)" `shouldBe` 
        (Just (App (App (App (Ref "f" 0) (Ref "a" 0) Eras) (Ref "b" 0) Eras) (Ref "c" 0) Eras))
    it "applying a lambda: \"((x) => x)(a,b)\"" $ do
      parse' expr "((x) => x)(a,b)" `shouldBe` 
        (Just (App (App (Lam "x" (Hol "#0") Keep (Var 0)) (Ref "a" 0) Keep) (Ref "b" 0) Keep))
    it "lambda style applications: \"(f a b c)\"" $ do
      parse' expr "(f a b c)" `shouldBe`
        (Just (App (App (App (Ref "f" 0) (Ref "a" 0) Keep) (Ref "b" 0) Keep) (Ref "c" 0) Keep))
    it "lambda style applications: \"(f (a b) c)\"" $ do
      parse' expr "(f (a b) c)" `shouldBe`
        (Just (App (App (Ref "f" 0) (App (Ref "a" 0) (Ref "b" 0) Keep) Keep) (Ref "c" 0) Keep))
      parse' expr "(f (a (b c)))" `shouldBe`
        (Just (App (Ref "f" 0) (App (Ref "a" 0) (App (Ref "b" 0) (Ref "c" 0) Keep) Keep) Keep))

  describe "Def" $ do
    it "bare-style definitions: \"a 1\"" $ do
      parse' def "a 1" `shouldBe` (Just ("a",Val 1))
    it "equals-style definitions: \"a = 1\"" $ do
      parse' def "a = 1" `shouldBe` (Just ("a",Val 1))
    it "definitions with arguments: \"a(x) 1\"" $ do
      parse' def "a(x) 1" `shouldBe` (Just ("a",Lam "x" (Hol "#0") Keep (Val 1)))
    it "definitions with arguments: \"a(x) x\"" $ do
      parse' def "a(x) x" `shouldBe` (Just ("a",Lam "x" (Hol "#0") Keep (Var 0)))
    it "equals-style definitions with arguments: \"a(x) = 1\"" $ do
      parse' def "a(x) = 1" `shouldBe` (Just ("a",Lam "x" (Hol "#0") Keep (Val 1)))
    it "definitions with types: \"a : Number 1\"" $ do
      parse' def "a : Number 1" `shouldBe` (Just ("a",Ann Num (Val 1)))
    it "definitions with types: \"a : Number = 1\"" $ do
      parse' def "a : Number = 1" `shouldBe` (Just ("a",Ann Num (Val 1)))
    it "definitions with arguments and types: \"a(A : Type, x : A) : A = x\"" $ do
      parse' def "a(A : Type, x : A) : A = x" `shouldBe`
        Just ("a"
        , Ann (All "A" Typ Keep (All "x" (Var 0) Keep (Var 1)))
              (Lam "A" Typ Keep (Lam "x" (Var 0) Keep (Var 0)))
        )

  describe "Let" $ do
    it "simple let" $ do
      parse' let_ "let x = 1; 2" `shouldBe`
        (Just $ Let (M.fromList [("x",Val 1)])  (Val 2))
    it "bare reference: \"x\"" $ do
      parse' term "x" `shouldBe` (Just (Ref "x" 0))
    it "referencing a Let: \"let x = 0; x\"" $ do
      parse' let_ "let x = 0; x" `shouldBe` 
        (Just $ Let (M.fromList [("x",Val 0)])  (Ref "x" 0))
    it "name-shadowing with let: \"let x = 1; let x = 0; x\"" $ do
      parse' let_ "let x = 1; let x = 0; x" `shouldBe`
        (Just $ Let (M.fromList [("x",Val 1)])  (Let (M.fromList [("x",Val 0)])  (Ref "x" 0)))
    it "unshadowing: \"let x = 1; let x = 0; ^x\"" $ do
      parse' let_ "let x = 1; let x = 0; ^x" `shouldBe`
        (Just $ Let (M.fromList [("x",Val 1)]) (Let (M.fromList [("x",Val 0)])  (Ref "x" 1)))
    it "referencing out of local scope: \"let x = 1; let x = 0; ^^x\"" $ do
      parse' let_ "let x = 1; let x = 0; ^^x" `shouldBe`
        (Just $ Let (M.fromList [("x",Val 1)])  $ Let (M.fromList [("x",Val 0)])  (Ref "x" 2))

    describe "mixing lets and lambdas" $ do
      it "\"let x = 2; let x = 1; ((x) => x)(0)\"" $ do
        parse' let_ "let x = 2; let x = 1; ((x) => x)(0)\"" `shouldBe`
          (Just $
            Let (M.fromList [("x",Val 2)]) $ Let (M.fromList [("x",Val 1)])
            (App (Lam "x" (Hol "#0") Keep (Var 0)) (Val 0) Keep)
          )
      it "\"let x = 2; let x = 1; ((x) => ^x)(0)\"" $ do
        parse' let_ "let x = 2; let x = 1; ((x) => ^x)(0)\"" `shouldBe`
          (Just $ 
            Let (M.fromList [("x",Val 2)]) $ Let (M.fromList [("x",Val 1)]) $
            (App (Lam "x" (Hol "#0") Keep (Ref "x" 0)) (Val 0) Keep)
          )
      it "\"let x = 2; let x = 1; ((x) => ^^x)(0)\"" $ do
        parse' term "let x = 2; let x = 1; ((x) => ^^x)(0)\"" `shouldBe`
          (Just $
            Let (M.fromList [("x",Val 2)]) $ Let (M.fromList [("x",Val 1)]) $
            (App (Lam "x" (Hol "#0") Keep (Ref "x" 1)) (Val 0) Keep)
          )
      it "\"let x = 2; let x = 1; ((x) => ^^^x)(0)\"" $ do
        parse' term "let x = 2; let x = 1; ((x) => ^^^x)(0)\"" `shouldBe`
          (Just $
            Let (M.fromList [("x",Val 2)]) $ Let (M.fromList [("x",Val 1)]) $
            (App (Lam "x" (Hol "#0") Keep (Ref "x" 2)) (Val 0) Keep)
          )
      it "\"((x) => let x = 1; let x = 0; x)(2)\"" $ do
        parse' term "((x) => let x = 1; let x = 0; x)(2)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 1)]) $ Let (M.fromList [("x",Val 0)]) $
              (Ref "x" 0))
            (Val 2) Keep)
      it "\"((x) => let x = 1; let x = 0; ^x)(2)\"" $ do
        parse' term "((x) => let x = 1; let x = 0; ^x)(2)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 1)]) $ Let (M.fromList [("x",Val 0)]) $
              (Ref "x" 1))
            (Val 2) Keep
          )
      it "\"((x) => let x = 1; let x = 0; ^^x)(2)\"" $ do
        parse' term "((x) => let x = 1; let x = 0; ^^x)(2)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 1)]) $ Let (M.fromList [("x",Val 0)]) $
              (Var 0))
            (Val 2) Keep
          )
      it "\"((x) => let x = 1; let x = 0; ^^^x)(2)\"" $ do
        parse' term "((x) => let x = 1; let x = 0; ^^^x)(2)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 1)]) $ Let (M.fromList [("x",Val 0)]) $
              (Ref "x" 2))
            (Val 2) Keep)
      it "\"((x) => let x = 2; ((x) => let x = 0; x)(1)(3)\"" $ do
        parse' term "((x) => let x = 2; ((x) => let x = 0; x)(1))(3)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 2)]) $
              (App (Lam "x" (Hol "#1") Keep $ Let (M.fromList [("x",Val 0)])  (Ref "x" 0))
                (Val 1) Keep))
            (Val 3) Keep)
      it "\"((x) => let x = 2; ((x) => let x = 0; ^x)(1)(3)\"" $ do
        parse' term "((x) => let x = 2; ((x) => let x = 0; ^x)(1))(3)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 2)]) $
                  (App (Lam "x" (Hol "#1") Keep $ Let (M.fromList [("x",Val 0)])  (Var 0))
                    (Val 1) Keep))
                (Val 3) Keep)

      it "\"((x) => let x = 2; ((x) => let x = 0; ^^x)(1))(3)\"" $ do
        parse' term "((x) => let x = 2; ((x) => let x = 0; ^^x)(1))(3)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 2)]) $
                  (App (Lam "x" (Hol "#1") Keep $ Let (M.fromList [("x",Val 0)]) (Ref "x" 1))
                    (Val 1) Keep))
            (Val 3) Keep)
      it "\"((x) => let x = 2; ((x) => let x = 0; ^^^x)(1))(3)\"" $ do
        parse' term "((x) => let x = 2; ((x) => let x = 0; ^^^x)(1))(3)" `shouldBe`
          (Just $
            App (Lam "x" (Hol "#0") Keep $ Let (M.fromList [("x",Val 2)]) $
              (App (Lam "x" (Hol "#1") Keep $ Let (M.fromList [("x",Val 0)]) (Var 1))
                (Val 1) Keep))
            (Val 3) Keep)

    describe "let block" $ do
      it "\"let (x = 1; y = 2); y\"" $ do
        parse' term "let (x = 1; y = 2); y" `shouldBe`
          (Just $ (Let (M.fromList [("x",Val 1),("y",Val 2)]) (Ref "y" 0)))
      it "\"let (x = 1, y = 2); y\"" $ do
        parse' term "let (x = 1, y = 2); y" `shouldBe`
          (Just $ (Let (M.fromList [("x",Val 1),("y",Val 2)]) (Ref "y" 0)))
      it "\"let (x = 1 y = 2) y\"" $ do
        parse' term "let (x = 1 y = 2); y" `shouldBe`
          (Just $ (Let (M.fromList [("x",Val 1),("y",Val 2)]) (Ref "y" 0)))
