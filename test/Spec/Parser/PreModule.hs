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
      parse' definition "a 1" `shouldBe` (Just $ Expr "a" (U64 1))
    it "semicolon-style definitions: \"a; 1\"" $ do
      parse' definition "a; 1" `shouldBe` (Just $ Expr "a" (U64 1))
    it "definitions with arguments: \"a(x) 1\"" $ do
      parse' definition "a(x) 1" `shouldBe` (Just $ Expr "a" (Lam "x" (Hol "#0") Keep (U64 1)))
    it "definitions with arguments: \"a(x) x\"" $ do
      parse' definition "a(x) x" `shouldBe` (Just $ Expr "a" (Lam "x" (Hol "#0") Keep (Var 0)))
    it "definitions with arguments (semicolon): \"a(x); 1\"" $ do
      parse' definition "a(x); 1" `shouldBe` (Just $ Expr "a"(Lam "x" (Hol "#0") Keep (U64 1)))
    it "definitions with types: \"a : Word 1\"" $ do
      parse' definition "a : Word 1" `shouldBe` (Just $ Expr "a" (Ann Wrd (U64 1)))
    it "definitions with types (semicolon): \"a : Word; 1\"" $ do
      parse' definition "a : Word; 1" `shouldBe` (Just $ Expr "a" (Ann Wrd (U64 1)))
    it "definitions with arguments and types: \"a(A : Type, x : A) : A; x\"" $ do
      parse' definition "a(A : Type, x : A) : A; x" `shouldBe`
        (Just $ Expr "a" (Ann (All "A" Typ Keep (All "x" (Var 0) Keep (Var 1)))
                             (Lam "A" Typ Keep (Lam "x" (Var 0) Keep (Var 0)))))

  describe "ADT" $ do
    it "T Empty" $ do
        parse' datatype "T Empty" `shouldBe` (Just $ ADT "Empty" [] [] M.empty)

    it "T Bool | true | false" $ do
        parse' datatype "T Bool | true | false" `shouldBe` 
          (Just $ ADT "Bool" [] [] 
            (M.fromList
              [ ("true", Ctor [] Nothing)
              , ("false", Ctor [] Nothing)
              ]
            )
          )
    it "T The{A} (x : A) | the(x : A) : The(A,x)" $ do
        parse' datatype "T The{A} (x : A) | the(x : A) : The(A,x)" `shouldBe`
          (Just $
            ADT "The" [("A", Hol "#0")] [("x", Var 0)]
              (M.fromList
                [("the"
                 , Ctor [("x", Var 0)]
                     (Just (App (App (Ref "The" 0 2) (Var 1) Keep) (Var 0) Keep)))
                ])
           )
    it "T Either{A,B} | lft(value : A) | rgt(value : B)" $ do
       parse' datatype "T Either{A,B} | lft(value : A) | rgt(value : B)" `shouldBe`
         (Just $
           ADT "Either" [("A", Hol "#0"), ("B",Hol "#1")] []
             (M.fromList
               [ ("lft", Ctor [("value", Var 1)] Nothing)
               , ("rgt", Ctor [("value", Var 0)] Nothing)
               ])
         )

  describe "Enum" $ do
    it "enum | FOO | BAR" $ do
      parse' enum "enum | FOO | BAR" `shouldBe` (Just $ Enum Nothing ["FOO", "BAR"])
      parse' enum "enum Foobar | FOO | BAR" `shouldBe`
        (Just $ Enum (Just "Foobar") ["FOO", "BAR"])

  describe "import" $ do
    it "import Nat" $ do
      parse' import_ "import Nat" `shouldBe` (Just $ Impt "Nat" "")

  describe "case expressions" $ do
    it "Empty" $ do
      parse' premodule "T Empty foo case x : Word" `shouldBe`
        (Just $ 
          [ Data (ADT "Empty" [] [] M.empty)
          , Expr "foo" (Cse (Ref "x" 0 0) [] M.empty (Just Wrd))
          ]
        )
    it "Bool" $ do
      parse' premodule
        "T Bool | true | false foo case true | true => 1 | false => 2" `shouldBe`
        (Just $ 
          [ Data (ADT "Bool" [] [] 
             (M.fromList
               [ ("true", Ctor [] Nothing)
               , ("false", Ctor [] Nothing)
               ]))
          , Expr "foo" (Cse (Ref "true" 0 0) [] 
              (M.fromList [("true",U64 1), ("false",U64 2)])
              Nothing)
          ]
        )
      parse' premodule
        "T Bool | true | false foo case true | false => 2 | true => 1" `shouldBe`
        (Just $ 
          [ Data (ADT "Bool" [] [] 
             (M.fromList
               [ ("true", Ctor [] Nothing)
               , ("false", Ctor [] Nothing)
               ]))
          , Expr "foo" (Cse (Ref "true" 0 0) [] 
              (M.fromList [("true",U64 1), ("false",U64 2)])
              Nothing)
          ]
        )
    it "Bool" $ do
      parse' premodule
        "foo case true | true => 1 | false => 2 T Bool | true | false" `shouldBe`
        (Just $
          [ Expr "foo" (Cse (Ref "true" 0 0) [] 
              (M.fromList [("true",U64 1), ("false",U64 2)])
              Nothing)
          , Data (ADT "Bool" [] [] 
             (M.fromList
               [ ("true", Ctor [] Nothing)
               , ("false", Ctor [] Nothing)
               ]))
          ]
        )
    --  parse' cse "case x | true => 1 | false => 0" `shouldBe`
    --    (Just $ Cse (Ref "x" 0) [] [("true", U64 1), ("false", U64 0)] Nothing)
    --it "\"as\" statement" $ do
    --  parse' cse "case x as y | true => 1 | false => 0" `shouldBe`
    --    (Just $ Cse (Ref "x" 0) [] [("true", U64 1), ("false", U64 0)] Nothing)
    --it "\"with\" statement" $ do
    --  parse' cse "case x with z with w | true => 1 | false => 0" `shouldBe`
    --    (Just $
    --      Cse (Ref "x" 0) [("z",Ref "z" 0, Hol "#0"), ("w",Ref "w" 0, Hol "#1")]
    --        [ ("true", U64 1)
    --        , ("false", U64 0)
    --        ] Nothing)
    --it "`\"as\" and \"with\" statements" $ do
    --  parse' cse "case x as y with z with w | true => 1 | false => 0" `shouldBe`
    --    (Just $
    --      Cse (Ref "x" 0) [("z",Ref "z" 0, Hol "#0"), ("w",Ref "w" 0, Hol "#1")]
    --        [ ("true", U64 1)
    --        , ("false", U64 0)
    --        ] Nothing)
    --
    --it "case inside let" $ do
    --  parse' term "let P = (x : Bool) => case x | true => y | false => z w" 
    --    `shouldBe`
    --    (Just $
    --      Let (M.fromList
    --      [ ("P", Lam "x" (Ref "Bool" 0) Keep 
    --          (Cse (Var 0) [] 
    --            [ ("true",Ref "y" 0)
    --            , ("false",Ref "z" 0)
    --            ] Nothing))
    --      ]) 
    --    (Ref "w" 0))
