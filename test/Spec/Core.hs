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
      eval' (Let "x" (Val 0) Norm (Ref "x" 0)) `shouldBe` (Val 0)
    it "name-shadowing with let: \"let x = 1; let x = 0; x\"" $ do
      eval' (Let "x" (Val 1) Norm (Let "x" (Val 0) Norm (Ref "x" 0))) `shouldBe`
        (Val 0)
    it "umbral referencing: \"let x = 1; let x = 0; ^x\"" $ do
      eval' (Let "x" (Val 1) Norm (Let "x" (Val 0) Norm (Ref "x" 1))) `shouldBe`
        (Val 1)
    it "referencing out of local scope: \"let x = 1; let x = 0; ^^x\"" $ do
      eval' (Let "x" (Val 1) Norm (Ref "x" 2)) `shouldBe` (Ref "x" 2)
    it "mixing lets and lambdas: \"let x = 2; let x = 1; ((x) => x)(0)\"" $ do
      eval'
        (Let "x" (Val 2) Norm $
         Let "x" (Val 1) Norm $
           (App (Lam "x" (Hol "#0") Keep (Var 0)) (Val 0) Keep)
        ) `shouldBe`
        (Val 0)
    it "mixing lets and lambdas: \"let x = 2; let x = 1; ((x) => ^x)(0)\"" $ do
      eval'
        (Let "x" (Val 2) Norm $
         Let "x" (Val 1) Norm $
         (App (Lam "x" (Hol "#0") Keep (Ref "x" 0)) (Val 0) Keep)
        ) `shouldBe`
        (Val 1)
    it "mixing lets and lambdas: \"let x = 2; let x = 1; ((x) => ^^x)(0)\"" $ do
      eval'
        (Let "x" (Val 2) Norm $
         Let "x" (Val 1) Norm $
         (App (Lam "x" (Hol "#0") Keep (Ref "x" 1)) (Val 0) Keep)
        ) `shouldBe`
        (Val 2)

    it "mixing lets and lambdas: \"let x = 2; let x = 1; ((x) => ^^^x)(0)\"" $ do
      eval'
        (Let "x" (Val 2) Norm $
         Let "x" (Val 1) Norm $
         (App (Lam "x" (Hol "#0") Keep (Ref "x" 2)) (Val 0) Keep)
        ) `shouldBe`
        (Ref "x" 2)

    it "mixing lets and lambdas: \"(x) => let x = 1; let x = 0; x)(2)\"" $ do
      eval'
        (App
          (Lam "x" (Hol "#0") Keep $
           Let "x" (Val 1) Norm $
           Let "x" (Val 0) Norm $
           (Ref "x" 0)
          )
          (Val 0) Keep
        ) `shouldBe`
        (Val 0)
    it "mixing lets and lambdas: \"((x) => let x = 1; let x = 0; ^x)(2)\"" $ do
      eval'
        (App
          (Lam "x" (Hol "#0") Keep $
           Let "x" (Val 1) Norm $
           Let "x" (Val 0) Norm $
           (Ref "x" 1)
          )
          (Val 0) Keep
        ) `shouldBe`
        (Val 1)
    it "mixing lets and lambdas: \"((x) => let x = 1; let x = 0; ^^x)(2)\"" $ do
      eval'
        (App
          (Lam "x" (Hol "#0") Keep $
           Let "x" (Val 1) Norm $
           Let "x" (Val 0) Norm $
           (Var 0)
          )
          (Val 2) Keep
        ) `shouldBe`
        (Val 2)

    it "mixing lets and lambdas: \"((x) => let x = 1; let x = 0; ^^^x)(2)\"" $ do
      eval'
        (App
          (Lam "x" (Hol "#0") Keep $
           Let "x" (Val 1) Norm $
           Let "x" (Val 0) Norm $
           (Ref "x" 2)
          )
          (Val 0) Keep
        ) `shouldBe`
        (Ref "x" 2)
