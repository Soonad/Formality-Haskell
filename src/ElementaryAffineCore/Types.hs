-- |
-- Module      : ElementaryAffineCore.Types
-- Copyright   : [2019] Serokell
-- License     : ?
--
-- Maintainer  : Serokell
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Main types of terms and expressions

module ElementaryAffineCore.Types where

import qualified Data.Map as M
import Data.Text (Text)

import Text.Megaparsec (SourcePos(..))

newtype Variable = Variable {getName :: Text}
  deriving Show

data Term =   Var {getVVar        :: Variable}
            | Lam {getLVar        :: [Variable] , getLExp         :: Exp}
            | App {getFirstAppExp :: Exp        , getSecondAppExp :: Exp}
            | Put {getBoxExp      :: Exp}
            | Dup {getDupVar      :: Variable   , getDupTerm      :: Exp, getInTerm :: Exp}
            deriving Show

-- | Expression contains a term (as a term or a link to a term)
data Exp = Exp {getPos :: SourcePos, getTerm :: Either Text Term, getEnv :: Exps}
  deriving Show

-- | Map between expressions and their names.
type Exps = M.Map Text Exp

data StratificationRule = FirstStratRule | SecondStratRule Int | ThirdStratRule Int
  deriving Show

data StratificationRuleBroken = StratificationRuleBroken StratificationRule SourcePos Variable
  deriving Show
