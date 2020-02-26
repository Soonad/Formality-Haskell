module Parser.Types where

import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Control.Monad              (void)
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy     hiding (All)

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Core                       (Eras (..), Name, Op (..))
import qualified Core                       as Core

-- binders can bind variables (deBruijn) or references
data Binder = VarB Name | RefB Name deriving (Eq, Show)

data ParseState = ParseState
  { _holeCount    :: Int      -- for generating unique metavariable names
  , _names        :: Set Name -- top level names
  } deriving Show

data ParseEnv = ParseEnv
  { _binders :: [Binder] -- binding contexts from lets, lambdas or foralls
  , _block   :: Set Name -- set of names in local `let` block
  } deriving Show

type Parser = RWST ParseEnv () ParseState (ParsecT Void Text Identity)

-- add top 
names :: [Name] -> Parser ()
names ns = modify (\s -> s {_names = Set.union (Set.fromList ns) (_names s)})

-- add a list of binders to the context
binders :: [Binder] -> Parser a -> Parser a
binders bs p = local (\e -> e { _binders = (reverse bs) ++ _binders e }) p

-- add names to current mutual recursion block
block :: [Name] -> Parser a -> Parser a
block n p = local (\e -> e { _block = Set.union (Set.fromList n) (_block e)}) p

-- a parser is a Reader-Writer-State monad transformer wrapped over a ParsecT
-- TODO : Custom error messages

initParseState = ParseState 0 Set.empty
initParseEnv   = ParseEnv [] Set.empty

