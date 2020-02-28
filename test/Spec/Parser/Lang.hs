module Spec.Parser.Lang where

import           Prelude                    hiding (log)

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Control.Monad.RWS.Lazy     hiding (All)

import           Core                       (Eras (..), Name, Op (..))
import           Lang
import           Parser.Lang
import           Spec.Parser.Utils

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
    it "reserved words fail: \"let\", \"T\"" $ do
      parse' name "let" `shouldBe` Nothing
      parse' name "T" `shouldBe` Nothing

  describe "Forall/Lambdas" $ do
    it "basic syntax: \"(A : Type) => A\"" $ do
      parse' allLam "(A : Type) => A" `shouldBe`
        (Just $ Lam "A" Typ Keep (Var 0))
      parse' allLam "(A : Type) -> A" `shouldBe`
        (Just $ All "A" Typ Keep (Var 0))

    it "erased arguments: \"(A : Type;) => A\"" $ do
      parse' allLam "(A : Type;) => A" `shouldBe`
        (Just $ Lam "A" Typ Eras (Var 0))
      parse' allLam "(A : Type;) -> A" `shouldBe`
        (Just $ All "A" Typ Eras (Var 0))

    it "multiple arguments: \"(A : Type, B : Type) => A\"" $ do
      parse' allLam "(A : Type, B : Type) => A" `shouldBe`
        (Just $ (Lam "A" Typ Keep (Lam "B" Typ Keep (Var 1))))
      parse' allLam "(A : Type, B : Type, C : Type) => A" `shouldBe`
        (Just $
          (Lam "A" Typ Keep (Lam "B" Typ Keep (Lam "C" Typ Keep (Var 2)))))

    it "holes for argument type: \"(A) => A\"" $ do
      parse' allLam "(A) => A" `shouldBe`
        (Just $ Lam "A" (Hol "#0") Keep (Var 0))
      parse' allLam "(A,B) => A" `shouldBe`
        (Just $ (Lam "A" (Hol "#0") Keep (Lam "B" (Hol "#1") Keep (Var 1))))

    it "anonymous arguments: \"(:Type) -> A\"" $ do
      parse' allLam "(:Type) -> A" `shouldBe`
        (Just $ All "_" Typ Keep (Ref "A" 0))
      parse' allLam "(:Type, :Type) -> A" `shouldBe`
        (Just $ All "_" Typ Keep (All "_" Typ Keep (Ref "A" 0)))


    it "correct deBruijn indices" $ do
      parse' allLam "(A : Type, x : A) -> A" `shouldBe`
        (Just $ (All "A" Typ Keep (All "x" (Var 0) Keep (Var 1))))
      parse' allLam "(A : Type, B : Type, x : A) -> A" `shouldBe`
        (Just $
          (All "A" Typ Keep (All "B" Typ Keep (All "x" (Var 1) Keep (Var 2)))))
      parse' allLam "(x : Word, Q : (y : Word) -> Type) -> Q(x)" `shouldBe`
        (Just $
          All "x" Wrd Keep
          (All "Q" (All "y" Wrd Keep Typ) Keep
          (App (Var 0) (Var 1) Keep)))
      parse' allLam "(x : Word, Q : Word -> Type) -> Q(x)" `shouldBe`
        (Just $
          All "x" Wrd Keep
          (All "Q" (All "_" Wrd Keep Typ) Keep
          (App (Var 0) (Var 1) Keep)))
  describe "Application" $ do
    it "function style applications: \"f(a)\"" $ do
      parse' term "f(a)" `shouldBe` (Just (App (Ref "f" 0) (Ref "a" 0) Keep))
    it "multiple arguments: \"f(a,b,c)\"" $ do
      parse' term "f(a,b)" `shouldBe`
        (Just (App (App (Ref "f" 0) (Ref "a" 0) Keep) (Ref "b" 0) Keep))
      parse' term "f(a,b,c)" `shouldBe`
        (Just
          (App (App (App
            (Ref "f" 0)
              (Ref "a" 0) Keep)
              (Ref "b" 0) Keep)
              (Ref "c" 0) Keep))
    it "parenthesized arguments: \"f(a)(b)(c)\"" $ do
      parse' term "f(a)(b)(c)" `shouldBe`
        (Just
          (App (App (App
            (Ref "f" 0)
            (Ref "a" 0) Keep)
            (Ref "b" 0) Keep)
            (Ref "c" 0) Keep))
    it "erased parenthesized arguments: \"f(a;)(b;)(c;)\"" $ do
      parse' term "f(a;)(b;)(c;)" `shouldBe`
        (Just
          (App (App (App
            (Ref "f" 0)
              (Ref "a" 0) Eras)
              (Ref "b" 0) Eras)
              (Ref "c" 0) Eras))
    it "erased arguments: \"f(a;b;c;)\"" $ do
      parse' term "f(a;b;c;)" `shouldBe`
        (Just
          (App (App (App
            (Ref "f" 0)
            (Ref "a" 0) Eras)
            (Ref "b" 0) Eras)
            (Ref "c" 0) Eras))
    it "applying a lambda: \"((x) => x)(a,b)\"" $ do
      parse' term "((x) => x)(a,b)" `shouldBe`
        (Just (App (App
          (Lam "x" (Hol "#0") Keep (Var 0))
          (Ref "a" 0) Keep)
          (Ref "b" 0) Keep))
    it "lambda style applications: \"(f a b c)\"" $ do
      parse' term "(f a b c)" `shouldBe`
        (Just (App (App (App
          (Ref "f" 0)
          (Ref "a" 0) Keep)
          (Ref "b" 0) Keep)
          (Ref "c" 0) Keep))
    it "lambda style applications: \"(f (a b) c)\"" $ do
      parse' term "(f (a b) c)" `shouldBe`
        (Just (App (App
          (Ref "f" 0)
          (App (Ref "a" 0) (Ref "b" 0) Keep) Keep)
          (Ref "c" 0) Keep))
      parse' term "(f (a (b c)))" `shouldBe`
        (Just
          (App (Ref "f" 0)
            (App (Ref "a" 0)
              (App (Ref "b" 0) (Ref "c" 0) Keep)
            Keep)
          Keep))

  describe "Let" $ do
    it "simple let" $ do
      parse' let_ "let x = 1; 2" `shouldBe`
        (Just $ Let (M.fromList [("x", U64 1)]) (U64 2))
    it "bare reference: \"x\"" $ do
      parse' term "x" `shouldBe` (Just (Ref "x" 0))
    it "referencing a Let: \"let x = 0; x\"" $ do
      parse' let_ "let x = 0; x" `shouldBe`
        (Just $ Let (M.fromList [("x",U64 0)]) (Ref "x" 0))
    it "name-shadowing with let: \"let x = 1; let x = 0; x\"" $ do
      parse' let_ "let x = 1; let x = 0; x" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 1)]) $
          Let (M.fromList [("x",U64 0)]) $
          (Ref "x" 0))
    it "unshadowing: \"let x = 1; let x = 0; ^x\"" $ do
      parse' let_ "let x = 1; let x = 0; ^x" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 1)]) $
          (Let (M.fromList [("x",U64 0)]) $
          (Ref "x" 1)))
    it "referencing out of local scope: \"let x = 1; let x = 0; ^^x\"" $ do
      parse' let_ "let x = 1; let x = 0; ^^x" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 1)]) $
          Let (M.fromList [("x",U64 0)]) $
          (Ref "x" 2))
    it "mixing lets and lambdas: ((x) => let x = 1; let x = 0; x)(2)" $ do
      parse' let_ "let x = 2; let x = 1; ((x) => x)(0)" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 2)]) $
          Let (M.fromList [("x",U64 1)]) $
          (App (Lam "x" (Hol "#0") Keep (Var 0)) (U64 0) Keep))
      parse' let_ "let x = 2; let x = 1; ((x) => ^x)(0)" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 2)]) $
          Let (M.fromList [("x",U64 1)]) $
          (App (Lam "x" (Hol "#0") Keep (Ref "x" 0)) (U64 0) Keep))
      parse' term "let x = 2; let x = 1; ((x) => ^^x)(0)" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 2)]) $
          Let (M.fromList [("x",U64 1)]) $
          (App (Lam "x" (Hol "#0") Keep (Ref "x" 1)) (U64 0) Keep))
      parse' term "let x = 2; let x = 1; ((x) => ^^^x)(0)" `shouldBe`
        (Just $
          Let (M.fromList [("x",U64 2)]) $
          Let (M.fromList [("x",U64 1)]) $
          (App (Lam "x" (Hol "#0") Keep (Ref "x" 2)) (U64 0) Keep))
      parse' term "((x) => let x = 1; let x = 0; x)(2)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
              Let (M.fromList [("x",U64 1)]) $
              Let (M.fromList [("x",U64 0)]) $
              (Ref "x" 0))
            (U64 2) Keep)
      parse' term "((x) => let x = 1; let x = 0; ^x)(2)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
              Let (M.fromList [("x",U64 1)]) $
              Let (M.fromList [("x",U64 0)]) $
              (Ref "x" 1))
            (U64 2) Keep)
      parse' term "((x) => let x = 1; let x = 0; ^^x)(2)" `shouldBe`
        (Just $
          App (Lam "x" (Hol "#0") Keep $
          Let (M.fromList [("x",U64 1)]) $
          Let (M.fromList [("x",U64 0)]) $
          (Var 0)) (U64 2) Keep)
      parse' term "((x) => let x = 1; let x = 0; ^^^x)(2)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
              Let (M.fromList [("x",U64 1)]) $
              Let (M.fromList [("x",U64 0)]) $
              (Ref "x" 2)) (U64 2) Keep)
      parse' term "((x) => let x = 2; ((x) => let x = 0; x)(1))(3)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
                Let (M.fromList [("x",U64 2)]) $
                (App
                  (Lam "x" (Hol "#1") Keep $
                  Let (M.fromList [("x",U64 0)])
                  (Ref "x" 0))
                  (U64 1) Keep))
            (U64 3) Keep)
      parse' term "((x) => let x = 2; ((x) => let x = 0; ^x)(1))(3)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
              Let (M.fromList [("x",U64 2)]) $
              (App
                (Lam "x" (Hol "#1") Keep $
                  Let (M.fromList [("x",U64 0)])
                  (Var 0))
                (U64 1)
                Keep))
            (U64 3)
            Keep)
      parse' term "((x) => let x = 2; ((x) => let x = 0; ^^x)(1))(3)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
            Let (M.fromList [("x",U64 2)]) $
            (App
              (Lam "x" (Hol "#1") Keep $
              Let (M.fromList [("x",U64 0)])
              (Ref "x" 1))
              (U64 1) Keep))
          (U64 3) Keep)
      parse' term "((x) => let x = 2; ((x) => let x = 0; ^^^x)(1))(3)" `shouldBe`
        (Just $
          App
            (Lam "x" (Hol "#0") Keep $
            Let (M.fromList [("x",U64 2)]) $
            (App
              (Lam "x" (Hol "#1") Keep $
              Let (M.fromList [("x",U64 0)]) $
              (Var 1))
              (U64 1) Keep))
            (U64 3) Keep)

    it "let block" $ do
      parse' term "let (x = 1; y = 2); y" `shouldBe`
        (Just $ (Let (M.fromList [("x",U64 1),("y",U64 2)]) (Ref "y" 0)))
      parse' term "let (x = 1 y = 2); y" `shouldBe`
        (Just $ (Let (M.fromList [("x",U64 1),("y",U64 2)]) (Ref "y" 0)))

  describe "case expressions" $ do
    it "Empty" $ do
      parse' cse "case x : Word" `shouldBe`
        (Just $ Cse (Ref "x" 0) [] [] (Just Wrd))
    it "Bool" $ do
      parse' cse "case x | true => 1 | false => 0" `shouldBe`
        (Just $ Cse (Ref "x" 0) [] [("true", U64 1), ("false", U64 0)] Nothing)
    it "\"as\" statement" $ do
      parse' cse "case x as y | true => 1 | false => 0" `shouldBe`
        (Just $ Cse (Ref "x" 0) [] [("true", U64 1), ("false", U64 0)] Nothing)
    it "\"with\" statement" $ do
      parse' cse "case x with z with w | true => 1 | false => 0" `shouldBe`
        (Just $
          Cse (Ref "x" 0) [(Ref "z" 0, Hol "#0"), (Ref "w" 0, Hol "#1")]
            [ ("true", U64 1)
            , ("false", U64 0)
            ] Nothing)
    it "`\"as\" and \"with\" statements" $ do
      parse' cse "case x as y with z with w | true => 1 | false => 0" `shouldBe`
        (Just $
          Cse (Ref "x" 0) [(Ref "z" 0, Hol "#0"), (Ref "w" 0, Hol "#1")]
            [ ("true", U64 1)
            , ("false", U64 0)
            ] Nothing)

  describe "when/switch" $ do
    it "when" $ do
      parse' whn "when | x => 0 else 1" `shouldBe`
        (Just $ Whn [(Ref "x" 0, U64 0)] (U64 1))
      parse' whn "when | x => 0 | y => 1 else 2" `shouldBe`
        (Just $ Whn [(Ref "x" 0, U64 0),(Ref "y" 0, U64 1)] (U64 2))
      parse' whn "when | x === a => 0 | y === b => 1 else 2" `shouldBe`
        (Just $
          Whn
            [ (Opr EQL (Ref "x" 0) (Ref "a" 0), U64 0)
            , (Opr EQL (Ref "y" 0) (Ref "b" 0), U64 1)
            ] (U64 2))
    it "switch" $ do
      parse' swt "switch x | a => 0 else 1" `shouldBe`
        (Just $ Swt (Ref "x" 0) [(Ref "a" 0, U64 0)] (U64 1))
      parse' swt "switch x | a => 0 | b => 2 else 1" `shouldBe`
        (Just $
          Swt (Ref "x" 0)
            [ (Ref "a" 0, U64 0)
            , (Ref "b" 0, U64 2)
            ] (U64 1))
  describe "ann/rewrite" $ do
    it "annotation" $ do
      parse' term "x :: t" `shouldBe` (Just $ Ann (Ref "t" 0) (Ref "x" 0))
    it "rewrite" $ do
      parse' term "x :: rewrite (x) => P(x) with e" `shouldBe`
        (Just $
          Ann
            (Rwt
              (Lam "x" (Hol "#0") Keep (App (Ref "P" 0) (Var 0) Keep))
              (Ref "e" 0))
            (Ref "x" 0))

  describe "character literals" $ do
    it "alphabetic" $ do
      parse' chr_ "\'a\'" `shouldBe` (Just $ Chr 'a')
      parse' chr_ "\'A\'" `shouldBe` (Just $ Chr 'A')
    it "numeric" $ do
      parse' chr_ "\'1\'" `shouldBe` (Just $ Chr '1')
      parse' chr_ "\'2\'" `shouldBe` (Just $ Chr '2')
    it "unicode" $ do
      parse' chr_ "\'δ\'" `shouldBe` (Just $ Chr 'δ')
      parse' chr_ "\'ヵ\'" `shouldBe` (Just $ Chr 'ヵ')
      parse' chr_ "\'😀\'" `shouldBe` (Just $ Chr '😀')
    it "escape" $ do
      parse' chr_ "\'\\n\'" `shouldBe` (Just $ Chr '\n')
      parse' chr_ "\'\\r\'" `shouldBe` (Just $ Chr '\r')
      parse' chr_ "\'\\NUL\'" `shouldBe` (Just $ Chr '\NUL')
      parse' chr_ "\'\\ACK\'" `shouldBe` (Just $ Chr '\ACK')
      parse' chr_ "\'\\xFF\'" `shouldBe` (Just $ Chr '\255')
      parse' chr_ "\'\\o77\'" `shouldBe` (Just $ Chr '?')
      parse' chr_ "\'\\255\'" `shouldBe` (Just $ Chr '\255')
      parse' chr_ "\'\\^@\'" `shouldBe` (Just $ Chr '\^@')
      parse' chr_ "\'\\^A\'" `shouldBe` (Just $ Chr '\^A')

  describe "string literals" $ do
    it "text" $
      parse' str "\"foobar\"" `shouldBe` (Just $ Str "foobar")
    it "string escape" $
      parse' str "\"foo\\&bar\"" `shouldBe` (Just $ Str "foobar")

 -- describe "word literals" $ do
 --   it "decimal" $

 --   it "binary" $


 --   it "hexadecimal" $

  describe "misc. integration" $ do
    it "opr from function application: \"P(a) -> A\"" $ do
      parse' term "P(a) -> A" `shouldBe`
        (Just $
          All "_" (App (Ref "P" 0) (Ref "a" 0) Keep) Keep
             (Ref "A" 0))
    it "case inside let" $ do
      parse' term "let P = (x : Bool) => case x | true => y | false => z w" 
        `shouldBe`
        (Just $
          Let (M.fromList
          [ ("P", Lam "x" (Ref "Bool" 0) Keep 
              (Cse (Var 0) [] 
                [ ("true",Ref "y" 0)
                , ("false",Ref "z" 0)
                ] Nothing))
          ]) 
        (Ref "w" 0))

    it "terms do not consume leading or trailing whitespace" $ do
      parse' (name <* eof) "a" `shouldBe` (Just $ "a")
      parse' (name <* eof) "a " `shouldBe` Nothing
      parse' (name <* eof) " a" `shouldBe` Nothing
      parse' (refVar <* eof) "a" `shouldBe` (Just $ Ref "a" 0)
      parse' (refVar <* eof) "a " `shouldBe` Nothing
      parse' (refVar <* eof) " a" `shouldBe` Nothing
      parse' (dbl <* eof) "Double" `shouldBe` (Just $ Dbl)
      parse' (dbl <* eof) "Double " `shouldBe` Nothing
      parse' (dbl <* eof) " Double" `shouldBe` Nothing
      parse' (f64 <* eof) "1.0" `shouldBe` (Just $ F64 1.0)
      parse' (f64 <* eof) "1.0 " `shouldBe` Nothing
      parse' (f64 <* eof) " 1.0" `shouldBe` Nothing
      parse' (wrd <* eof) "Word" `shouldBe` (Just $ Wrd)
      parse' (wrd <* eof) "Word " `shouldBe` Nothing
      parse' (wrd <* eof) " Word" `shouldBe` Nothing
      parse' (u64 <* eof) "1" `shouldBe` (Just $ U64 1)
      parse' (u64 <* eof) "1 " `shouldBe` Nothing
      parse' (u64 <* eof) " 1" `shouldBe` Nothing
      parse' (str <* eof) "\"\"" `shouldBe` (Just $ Str "")
      parse' (str <* eof) "\"\" " `shouldBe` Nothing
      parse' (str <* eof) " \"\"" `shouldBe` Nothing
      parse' (chr_ <* eof) "'a'" `shouldBe` (Just $ Chr 'a')
      parse' (chr_ <* eof) "'a' " `shouldBe` Nothing
      parse' (chr_ <* eof) " 'a'" `shouldBe` Nothing
      parse' (lst <* eof) "[]" `shouldBe` (Just $ Lst [])
      parse' (lst <* eof) "[] " `shouldBe` Nothing
      parse' (lst <* eof) " []" `shouldBe` Nothing
      parse' (slf <* eof) "${x} A" `shouldBe` (Just $ Slf "x" (Ref "A" 0))
      parse' (slf <* eof) " ${x} A" `shouldBe` Nothing
      parse' (slf <* eof) "${x} A " `shouldBe` Nothing
      parse' (new <* eof) "new(A) x" `shouldBe` (Just $ New (Ref "A" 0) (Ref "x" 0))
      parse' (new <* eof) " new(A) x" `shouldBe` Nothing
      parse' (new <* eof) "new(A) x " `shouldBe` Nothing
      parse' (log <* eof) "log(A) x" `shouldBe` (Just $ Log (Ref "A" 0) (Ref "x" 0))
      parse' (log <* eof) " log(A) x" `shouldBe` Nothing
      parse' (log <* eof) "log(A) x " `shouldBe` Nothing
      -- use
      -- ite
      -- hol
      -- refVar
      -- cse
      -- whn
      -- swt


-- Problems:
-- "-1" syntax
-- Pair literal
-- get
-- dictionary literal
-- do notation
-- with as
-- rewrite . syntax

