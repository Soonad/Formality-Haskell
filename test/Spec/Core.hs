module Spec.Core where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import qualified Data.Map.Strict as M


import Core

eval' :: Term -> Term
eval' x = eval x M.empty

spec :: SpecWith ()
spec = do
  describe "Application" $ do
    it "applying a lambda: \"((x) => x)(1) ~> 1\"" $ do
      eval' (App (Lam "x" (Hol "#0") Keep (Var 0)) (Val 1) Keep) `shouldBe` (Val 1)

  describe "References" $ do
    it "bare reference: \"x\"" $ do
      eval' (Ref "x" 0) `shouldBe` (Ref "x" 0)
    it "referencing a Let: \"let x = 0; x\"" $ do
      eval' (Let [("x",(Val 0))]  (Ref "x" 0)) `shouldBe` (Val 0)
    it "name-shadowing with let: \"let x = 1; let x = 0; x\"" $ do
      eval' (Let [("x",(Val 1))]  (Let [("x",(Val 0))]  (Ref "x" 0))) `shouldBe`
        (Val 0)
    it "umbral referencing: \"let x = 1; let x = 0; ^x\"" $ do
      eval' (Let [("x",(Val 1))]  (Let [("x",(Val 0))]  (Ref "x" 1))) `shouldBe`
        (Val 1)
    it "referencing out of local scope: \"let x = 1; let x = 0; ^^x\"" $ do
      eval' (Let [("x",(Val 1))]  (Ref "x" 2)) `shouldBe` (Ref "x" 2)

    describe "mixing lets and lambdas" $ do
      it "\"let x = 2; let x = 1; ((x) => x)(0)\"" $ do
        eval'
          (Let [("x",(Val 2))]  $
           Let [("x",(Val 1))]  $
             (App (Lam "x" (Hol "#0") Keep (Var 0)) (Val 0) Keep)
          ) `shouldBe`
          (Val 0)
      it "\"let x = 2; let x = 1; ((x) => ^x)(0)\"" $ do
        eval'
          (Let [("x",(Val 2))]  $
           Let [("x",(Val 1))]  $
           (App (Lam "x" (Hol "#0") Keep (Ref "x" 0)) (Val 0) Keep)
          ) `shouldBe`
          (Val 1)
      it "\"let x = 2; let x = 1; ((x) => ^^x)(0)\"" $ do
        eval'
          (Let [("x",(Val 2))] $
           Let [("x",(Val 1))] $
           (App (Lam "x" (Hol "#0") Keep (Ref "x" 1)) (Val 0) Keep)
          ) `shouldBe`
          (Val 2)

      it "\"let x = 2; let x = 1; ((x) => ^^^x)(0)\"" $ do
        eval'
          (Let [("x",(Val 2))]  $
           Let [("x",(Val 1))]  $
           (App (Lam "x" (Hol "#0") Keep (Ref "x" 2)) (Val 0) Keep)
          ) `shouldBe`
          (Ref "x" 2)

      it "\"(x) => let x = 1; let x = 0; x)(2)\"" $ do
        eval'
          (App
            (Lam "x" (Hol "#0") Keep $
             Let [("x",(Val 1))]  $
             Let [("x",(Val 0))]  $
             (Ref "x" 0)
            )
            (Val 0) Keep
          ) `shouldBe`
          (Val 0)
      it "\"((x) => let x = 1; let x = 0; ^x)(2)\"" $ do
        eval'
          (App
            (Lam "x" (Hol "#0") Keep $
             Let [("x",(Val 1))]  $
             Let [("x",(Val 0))]  $
             (Ref "x" 1)
            )
            (Val 0) Keep
          ) `shouldBe`
          (Val 1)
      it "\"((x) => let x = 1; let x = 0; ^^x)(2)\"" $ do
        eval'
          (App
            (Lam "x" (Hol "#0") Keep $
             Let [("x",(Val 1))]  $
             Let [("x",(Val 0))]  $
             (Var 0)
            )
            (Val 2) Keep
          ) `shouldBe`
          (Val 2)

      it "\"((x) => let x = 1; let x = 0; ^^^x)(2)\"" $ do
        eval'
          (App
            (Lam "x" (Hol "#0") Keep $
             Let [("x",(Val 1))] $
             Let [("x",(Val 0))] $
             (Ref "x" 2)
            )
            (Val 0) Keep
          ) `shouldBe`
          (Ref "x" 2)
    describe "let block" $ do
      it "\"let (x = 1; y = 2); x\"" $ do
        eval'
          (App
            (Lam "x" (Hol "#0") Keep $
             Let [("x",Val 1), ("y",Val 2)] $
             (Ref "x" 0)
            )
            (Val 0) Keep
          ) `shouldBe`
          (Val 1)
      it "\"let (x = 1; y = 2); let (x = 3; y = 4); ^x\"" $ do
        eval'
          (App
            (Lam "x" (Hol "#0") Keep $
             Let [("x",Val 1), ("y",Val 2)] $
             Let [("x",Val 3), ("y",Val 4)] $
             (Ref "x" 1)
            )
            (Val 0) Keep
          ) `shouldBe`
          (Val 1)
      it "\"let (f(x,y) = x; y = f(1,2)); y\"" $ do
        eval'
          (Let
            [ ("f",Lam "x" (Hol "#0") Keep (Lam "y" (Hol "#1") Keep (Var 1)))
            , ("y",App (App (Ref "f" 0) (Val 1) Keep) (Val 2) Keep)
            ]
            (Ref "y" 0)
          ) `shouldBe`
          (Val 1)

      it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isEven(42)\"" $ do
        eval'
          (Let [ ("isOdd", Lam "x" (Hol "#0") Keep 
                      (Ite (Op2 EQL (Var 0) (Val 1)) (Val 1) 
                        (App (Ref "isEven" 0) (Op2 SUB (Var 0) (Val 1)) Keep)))
               , ("isEven", Lam "x" (Hol "#1") Keep 
                      (Ite (Op2 EQL (Var 0) (Val 1)) (Val 0) 
                        (App (Ref "isOdd" 0) (Op2 SUB (Var 0) (Val 1)) Keep)))
               ] (App (Ref "isEven" 0) (Val 42) Keep)
           ) `shouldBe` (Val 1)

      it "\"let (isOdd(x) = if x == 1 then 1 else isEven(x - 1); isEven(x) = if x == 1 then 0 else isOdd(x - 1);); isOdd(43)\"" $ do
        eval'
          (Let [ ("isOdd", Lam "x" (Hol "#0") Keep 
                      (Ite (Op2 EQL (Var 0) (Val 1)) (Val 1) 
                        (App (Ref "isEven" 0) (Op2 SUB (Var 0) (Val 1)) Keep)))
               , ("isEven", Lam "x" (Hol "#1") Keep 
                      (Ite (Op2 EQL (Var 0) (Val 1)) (Val 0) 
                        (App (Ref "isOdd" 0) (Op2 SUB (Var 0) (Val 1)) Keep)))
               ] (App (Ref "isOdd" 0) (Val 43) Keep)
           ) `shouldBe` (Val 1)
