{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes #-}
-- |
-- Module      : ElementaryAffineCore.StratificationChecker
-- Copyright   : [2019] Sunshine Cybernetics
-- License     : MIT
--
-- Maintainer  : Sunshine Cybernetics
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Check terms for the stratification rules

module ElementaryAffineCore.StratificationChecker where

import Control.Monad.Except (Except,forM_, throwError)
import Data.Functor (($>))
import qualified Data.Map as M
import Data.Text (Text)

import ElementaryAffineCore.Types

data NumberOfUsages = Zero | One
  deriving Show

type NumberOfBoxes = NumberOfUsages

type RTerm = Term 'Raw

type RExp = Expression 'Raw

-- | Check all three stratification rules
checkExp :: RExp -> Except StratificationRuleBroken ()
checkExp e = checkFirstRule e *> checkSecondRule e *> checkThirdRule e


-- | Check that variables bound by lambdas are used at most once.
checkFirstRule :: RExp -> Except StratificationRuleBroken ()
checkFirstRule (ExpRaw pos term env) =
    case term of
        Lam vars e ->
            let boundedVarName = getName vars
            in checkBoundedVarFirst Zero e boundedVarName *> return ()
        App e1 e2 -> checkFirstRule e1 *> checkFirstRule e2
        Put e -> checkFirstRule e
        Dup _ dupTerm inTerm -> checkFirstRule dupTerm *> checkFirstRule inTerm
        Var _ -> return ()
        Link name -> forM_ (M.lookup name env) checkFirstRule

-- | Check that there is exactly 0 boxes between a variable bound by a lambda and its occurrence.
checkSecondRule :: RExp -> Except StratificationRuleBroken ()
checkSecondRule (ExpRaw pos term env) =
    case term of
        Lam vars e ->
            let boundedVarName = getName vars
            in checkBoundedVarBoxes 0 e boundedVarName $> ()
        App e1 e2 -> checkSecondRule e1 *> checkSecondRule e2
        Put e -> checkSecondRule e
        Dup _ dupTerm inTerm -> checkSecondRule dupTerm *> checkSecondRule inTerm
        Var _ -> return ()
        Link name -> forM_ (M.lookup name env) checkSecondRule

-- | Check that there is exactly 1 box between a variable bound by a duplication and its occurrence.
checkThirdRule :: RExp -> Except StratificationRuleBroken ()
checkThirdRule (ExpRaw pos term env) =
    case term of
        Lam vars e -> checkThirdRule e
        App e1 e2 -> checkThirdRule e1 *> checkThirdRule e2
        Put e -> checkThirdRule e
        Dup var dupTerm inTerm ->
          let dupVarName = getName var
          in checkDupVar 0 inTerm dupVarName *> return ()
        Var _ -> return ()
        Link name -> forM_ (M.lookup name env) checkThirdRule

-- Auxillary functions

checkBoundedVarFirst :: NumberOfUsages -> RExp -> Text -> Except StratificationRuleBroken NumberOfUsages
checkBoundedVarFirst alreadyUsed (ExpRaw pos term env) name =
    case term of
        Var v@(Variable nameIn) ->
          if name == nameIn
          then case alreadyUsed of
            Zero -> return One
            One  -> throwError $ StratificationRuleBroken FirstStratRule pos v
          else return alreadyUsed
        App exp1 exp2 -> do
            n1 <- checkBoundedVarFirst alreadyUsed exp1 name
            checkBoundedVarFirst n1 exp2 name
        Put e -> checkBoundedVarFirst alreadyUsed e name
        Dup (Variable dupName) dupTerm inTerm ->
          if name == dupName
          then return alreadyUsed
          else do
            n1 <- checkBoundedVarFirst alreadyUsed dupTerm name
            checkBoundedVarFirst n1 inTerm name
        Lam var e -> do
            let boundedVarName = getName var
            (if name == boundedVarName
             then return alreadyUsed
             else checkBoundedVarFirst alreadyUsed e name) <* checkBoundedVarFirst Zero e boundedVarName
        Link name -> case M.lookup name env of
          Just exp -> checkFirstRule exp $> alreadyUsed
          Nothing  -> return alreadyUsed

checkBoundedVarBoxes :: Int -> RExp -> Text -> Except StratificationRuleBroken Int
checkBoundedVarBoxes numOfBoxes (ExpRaw pos term env) name =
    case term of
        Var v@(Variable nameIn) ->
          if name == nameIn && numOfBoxes /= 0
          then throwError $ StratificationRuleBroken (SecondStratRule numOfBoxes) pos v
          else return numOfBoxes
        App exp1 exp2 -> do
            n1 <- checkBoundedVarBoxes numOfBoxes exp1 name
            checkBoundedVarBoxes n1 exp2 name
        Put e -> checkBoundedVarBoxes (numOfBoxes + 1) e name
        Dup (Variable dupName) dupTerm inTerm -> do
            n1 <- if name == dupName
                  then checkBoundedVarBoxes 0 dupTerm name
                  else checkBoundedVarBoxes numOfBoxes dupTerm name
            checkBoundedVarBoxes n1 inTerm name
        Lam var e -> do
            let boundedVarName = getName var
            (if name == boundedVarName
             then return numOfBoxes
             else checkBoundedVarBoxes numOfBoxes e name) <* checkBoundedVarBoxes 0 e boundedVarName
        Link name -> case M.lookup name env of
          Just exp -> checkSecondRule exp $> numOfBoxes
          Nothing  -> return numOfBoxes

checkDupVar :: Int -> RExp -> Text -> Except StratificationRuleBroken Int
checkDupVar numOfBoxes (ExpRaw pos term env) name =
    case term of
        Var v@(Variable nameIn) ->
          if name == nameIn && numOfBoxes /= 1
          then throwError $ StratificationRuleBroken (ThirdStratRule numOfBoxes) pos v
          else return numOfBoxes
        App exp1 exp2 -> do
            n1 <- checkDupVar numOfBoxes exp1 name
            checkDupVar n1 exp2 name
        Put e -> checkDupVar (numOfBoxes + 1) e name
        Dup (Variable dupName) dupTerm inTerm -> do
            n1 <- if name == dupName
                  then checkDupVar 0 dupTerm name
                  else checkDupVar numOfBoxes dupTerm name *> checkDupVar 0 dupTerm dupName
            checkDupVar n1 inTerm name
        Lam _ e -> checkDupVar numOfBoxes e name
        Link name -> case M.lookup name env of
          Just exp -> checkThirdRule exp $> numOfBoxes
          Nothing  -> return numOfBoxes
