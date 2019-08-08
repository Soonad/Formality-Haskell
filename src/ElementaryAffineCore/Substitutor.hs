{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedStrings  #-}
-- |
-- Module      : ElementaryAffineCore.Substitutor
-- Copyright   : [2019] Sunshine Cybernetics
-- License     : MIT
--
-- Maintainer  : Sunshine Cybernetics
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Substitution of local definitions.

module ElementaryAffineCore.Substitutor
  (substituteLocalEnvironment
  , type WarningInfo) where

import Control.Monad.Except
import Control.Monad.Writer (Writer, tell)
import Text.Megaparsec (SourcePos(..))
import qualified Data.Map as M
import Data.Text

import ElementaryAffineCore.Types

type WarningInfo = (Warning,SourcePos)

-- | Substitute local expressions in a list of global terms.
substituteLocalEnvironment
  :: Environment 'Raw
  -> Writer [WarningInfo] (Environment 'Final)
substituteLocalEnvironment globalEnvironment =
    let globalExpNames = M.keys globalEnvironment
    in mapM (removeLocalEnvironment globalExpNames M.empty) globalEnvironment


-- | Substitute local expressions, rename variables, and transform unknown links to free variables.
-- Free variable is a cause of a warning.
removeLocalEnvironment
  :: [Text]
  -> Environment 'Raw
  -> Expression 'Raw
  -> Writer [WarningInfo] (Expression 'Final)
removeLocalEnvironment globalTerms env (ExpRaw pos term localEnv) =
  let envAcc = M.union localEnv env
  in case term of
       Var v        -> return $ Exp pos (Var v)
       Lam var body -> Exp pos . Lam var <$>
           removeLocalEnvironment globalTerms envAcc body
       App term arg ->
           do
             newTerm <- removeLocalEnvironment globalTerms envAcc term
             newArg  <- removeLocalEnvironment globalTerms envAcc arg
             return $ Exp pos $ App newTerm newArg
       Put term -> Exp pos . Put <$> removeLocalEnvironment globalTerms envAcc term
       Dup var term body ->
             do
               newTerm <- removeLocalEnvironment globalTerms envAcc body
               newBody <- removeLocalEnvironment globalTerms envAcc term
               return $ Exp pos $ Dup var newTerm newBody
       Reference name -> case M.lookup name envAcc of
           Just exp -> removeLocalEnvironment globalTerms M.empty exp
           Nothing ->
               if name `elem` globalTerms
               then return $ Exp pos $ Reference name
               else do
                 tell [(FreeVariable (Variable name),pos)]
                 return $ Exp pos $ Var (Variable $ "f:" <> name)
