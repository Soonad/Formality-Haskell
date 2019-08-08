{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE NoStarIsType         #-}
-- |
-- Module      : ElementaryAffineCore.Types
-- Copyright   : [2019] Sunshine Cybernetics
-- License     : MIT
--
-- Maintainer  : Sunshine Cybernetics
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Main types with terms and expressions

module ElementaryAffineCore.Types
  ( -- * Common data types
    Environment
  , Exp(..)
  , ExpRaw (..)
  , Expression
  , ExpType (..)
  , Term (..)
  , Variable (..)

  -- * Errors and warnings
  , StratificationRule (..)
  , StratificationRuleBroken (..)
  , Warning (..)
  ) where

import Data.Kind (Type)
import Data.Text (Text)
import Text.Megaparsec (SourcePos(..))

import qualified Data.Map as M

newtype Variable = Variable {getName :: Text}
  deriving (Eq, Ord, Show)

-- | Possible types of terms. Raw terms are used only before the substitution phase.
data ExpType = Raw | Final deriving Show

-- | Corresponding type of expression.
type family Expression (t :: ExpType) :: Type where
    Expression 'Raw = ExpRaw
    Expression 'Final = Exp

-- | Main term data type. Raw term contains expressions with local variables as environment.
data Term (typeOfExp :: ExpType) = Show (Expression typeOfExp) =>
      Var        { getVVar    :: Variable}
    | Lam        { getLVar    :: Variable
                 , getLExp    :: Expression typeOfExp}
    | App        { getAppExp  :: Expression typeOfExp
                 , getArgExp  :: Expression typeOfExp}
    | Put        { getBoxExp  :: Expression typeOfExp}
    | Dup        { getDupVar  :: Variable
                 , getDupTerm :: Expression typeOfExp
                 , getInTerm  :: Expression typeOfExp}
    | Reference  { getRef     :: Text}

deriving instance (Show (Expression typeOfExp)) => Show (Term typeOfExp)

-- | Raw expression contains a term, its position in a source file and environment (local definitions)
data ExpRaw = ExpRaw {getRPos :: SourcePos, getRTerm :: Term 'Raw, getEnv :: Environment 'Raw}
  deriving Show
-- | Expression contains a term and its position in a source file.
data Exp = Exp {getPos :: SourcePos, getTerm :: Term 'Final}
  deriving Show

-- | Map between expressions and their names.
type Environment typeOfExp = M.Map Text (Expression typeOfExp)

data StratificationRule = FirstStratRule | SecondStratRule Int | ThirdStratRule Int
  deriving Show

-- | Type containing information about stratification error.
data StratificationRuleBroken = StratificationRuleBroken StratificationRule SourcePos Variable
  deriving Show

-- | Possible warnings.
data Warning = FreeVariable Variable
  deriving Show
