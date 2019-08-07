{-# LANGUAGE DataKinds, ExplicitNamespaces, OverloadedStrings #-}
-- |
-- Module      : ElementaryAffineCore.Substitutor
-- Copyright   : [2019] Sunshine Cybernetics
-- License     : MIT
--
-- Maintainer  : Sunshine Cybernetics
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Substitute local definitions.

module ElementaryAffineCore.Substitutor (substituteLocalExps, type WarningInfo) where

import Control.Monad.Except
import Control.Monad.Writer (Writer, tell)
import Text.Megaparsec (SourcePos(..))
import qualified Data.Map as M
import Data.Text

import ElementaryAffineCore.Types

type WarningInfo = (Warning,SourcePos)

-- | Substitute local expressions in a list of global terms.
substituteLocalExps :: Exps 'Raw -> Writer [WarningInfo] (Exps 'Final)
substituteLocalExps globalExps =
    let globalExpNames = M.keys globalExps
    in mapM (removeLocalExps globalExpNames) globalExps


-- | Substitute local expressions, rename variables, and transform unknown links to free variables.
-- Free variable is a cause of a warning.
removeLocalExps :: [Text] -> Expression 'Raw -> Writer [WarningInfo] (Expression 'Final)
removeLocalExps globalTerms (ExpRaw pos term env) = case term of
    Var v@(Variable name) -> return $ Exp pos (Var v)
    Lam var (ExpRaw posLocal term envLocal) -> Exp pos . Lam var <$> removeLocalExps globalTerms (ExpRaw posLocal term (M.union envLocal env))
    App (ExpRaw posLocal1 term1 envLocal1) (ExpRaw posLocal2 term2 envLocal2) ->
        do
          exp1 <- removeLocalExps globalTerms (ExpRaw posLocal1 term1 (M.union envLocal1 env))
          exp2 <- removeLocalExps globalTerms (ExpRaw posLocal2 term2 (M.union envLocal2 env))
          return $ Exp pos $ App exp1 exp2
    Put (ExpRaw posLocal term envLocal) -> Exp pos . Put <$> removeLocalExps globalTerms (ExpRaw posLocal term (M.union envLocal env))
    Dup var (ExpRaw posLocal1 term1 envLocal1) (ExpRaw posLocal2 term2 envLocal2) ->
        do
          exp1 <- removeLocalExps globalTerms (ExpRaw posLocal1 term1 (M.union envLocal1 env))
          exp2 <- removeLocalExps globalTerms (ExpRaw posLocal2 term2 (M.union envLocal2 env))
          return $ Exp pos $ Dup var exp1 exp2
    Link name -> case M.lookup name env of
        Just exp -> do
            expToRename <- removeLocalExps globalTerms exp
            return $ renameVariables name expToRename
        Nothing ->
            if name `elem` globalTerms
            then return $ Exp pos $ Link name
            else do
              tell [(FreeVariable (Variable name),pos)]
              return $ Exp pos $ Var (Variable name)

-- | Rename variables in a local term body after substitution. New names are in form of "(link name):(variable name)"
renameVariables :: Text -> Expression 'Final -> Expression 'Final
renameVariables linkName (Exp pos term) = Exp pos $ case term of
    Var (Variable name)           -> Var (Variable $ linkName <> ":" <> name)
    Lam (Variable name) exp       -> Lam (Variable $ linkName <> ":" <> name) $ renameVariables linkName exp
    App exp1 exp2                 -> App (renameVariables linkName exp1) (renameVariables linkName exp2)
    Put exp                       -> Put $ renameVariables linkName exp
    Dup (Variable name) exp1 exp2 -> Dup (Variable $ linkName <> ":" <> name) (renameVariables linkName exp1) (renameVariables linkName exp2)
    l@(Link _)                    -> l
