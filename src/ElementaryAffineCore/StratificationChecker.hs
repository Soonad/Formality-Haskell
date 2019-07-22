{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      : ElementaryAffineCore.StratificationChecker
-- Copyright   : [2019] Serokell
-- License     : ?
--
-- Maintainer  : Serokell
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Check terms for the stratification rules

module ElementaryAffineCore.StratificationChecker where

import Control.Monad.Except
import qualified Data.Map as M
import Data.Text

import ElementaryAffineCore.Types

data NumberOfUsages = Zero | One
  deriving Show

type NumberOfBoxes = NumberOfUsages

checkTerm :: Exp -> Except StratificationRuleBroken ()
checkTerm e = checkFirstRule e *> checkSecondRule e *> checkThirdRule e


-- | Check that variables bound by lambdas are used at most once.
checkFirstRule :: Exp -> Except StratificationRuleBroken ()
checkFirstRule (Exp pos (Right term) env) =
    case term of
        Lam vars e ->
            let boundedVarNames = getName <$> vars
            in mapM_ (checkBoundedVarFirst Zero e) boundedVarNames
        App e1 e2 -> checkFirstRule e1 *> checkFirstRule e2
        Put e -> checkFirstRule e
        Dup _ dupTerm inTerm -> checkFirstRule dupTerm *> checkFirstRule inTerm
        Var _ -> return ()
checkFirstRule _ = return ()

-- | Check that there is exactly 0 boxes between a variable bound by a lambda and its occurrence.
checkSecondRule :: Exp -> Except StratificationRuleBroken ()
checkSecondRule (Exp pos (Right term) env) =
    case term of
        Lam vars e ->
            let boundedVarNames = getName <$> vars
            in mapM_ (checkBoundedVarSecond 0 e) boundedVarNames
        App e1 e2 -> checkSecondRule e1 *> checkSecondRule e2
        Put e -> checkSecondRule e
        Dup _ dupTerm inTerm -> checkSecondRule dupTerm *> checkSecondRule inTerm
        Var _ -> return ()
checkSecondRule _ = return ()

-- | Check that there is exactly 1 box between a variable bound by a duplication and its occurrence.
checkThirdRule :: Exp -> Except StratificationRuleBroken ()
checkThirdRule (Exp pos (Right term) env) =
    case term of
        Lam vars e -> checkThirdRule e
        App e1 e2 -> checkThirdRule e1 *> checkThirdRule e2
        Put e -> checkThirdRule e
        Dup var dupTerm inTerm ->
          let dupVarName = getName var
          in checkDupVar 0 inTerm dupVarName *> return ()
        Var _ -> return ()
checkThirdRule _ = return ()

-- Auxillary functions

checkBoundedVarFirst :: NumberOfUsages -> Exp -> Text -> Except StratificationRuleBroken NumberOfUsages
checkBoundedVarFirst alreadyUsed (Exp _ (Left _) _) _ = return alreadyUsed
checkBoundedVarFirst alreadyUsed (Exp pos (Right term) _) name =
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
        Lam vars e -> do
            let boundedVarNames = getName <$> vars
            (if elem name boundedVarNames
             then return alreadyUsed
             else checkBoundedVarFirst alreadyUsed e name) <* mapM_ (checkBoundedVarFirst Zero e) boundedVarNames

checkBoundedVarSecond :: Int -> Exp -> Text -> Except StratificationRuleBroken Int
checkBoundedVarSecond numOfBoxes (Exp _ (Left _) _) _ = return numOfBoxes
checkBoundedVarSecond numOfBoxes (Exp pos (Right term) _) name =
    case term of
        Var v@(Variable nameIn) ->
          if name == nameIn && numOfBoxes /= 0
          then throwError $ StratificationRuleBroken (SecondStratRule numOfBoxes) pos v
          else return numOfBoxes
        App exp1 exp2 -> do
            n1 <- checkBoundedVarSecond numOfBoxes exp1 name
            checkBoundedVarSecond n1 exp2 name
        Put e -> checkBoundedVarSecond (numOfBoxes + 1) e name
        Dup (Variable dupName) dupTerm inTerm -> do
            n1 <- if name == dupName
                  then checkBoundedVarSecond 0 dupTerm name
                  else checkBoundedVarSecond numOfBoxes dupTerm name
            checkBoundedVarSecond n1 inTerm name
        Lam vars e -> do
            let boundedVarNames = getName <$> vars
            (if elem name boundedVarNames
             then return numOfBoxes
             else checkBoundedVarSecond numOfBoxes e name) <* mapM_ (checkBoundedVarSecond 0 e) boundedVarNames

checkDupVar :: Int -> Exp -> Text -> Except StratificationRuleBroken Int
checkDupVar numOfBoxes (Exp _ (Left _) _) _ = return numOfBoxes
checkDupVar numOfBoxes (Exp pos (Right term) _) name =
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
                  else checkDupVar numOfBoxes dupTerm name
            checkDupVar n1 inTerm name
