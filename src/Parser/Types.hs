module Parser.Types where

import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import           Control.Monad              (void)
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy     hiding (All)

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Core                       (Eras (..), Name, Op (..))
import qualified Core                       as Core

import qualified Lang as Lang

-- binders can bind variables (deBruijn) or references
data Binder = VarB Name | RefB Name deriving (Eq, Show)

data ParseState = ParseState
  { _holeCount    :: Int      -- for generating unique metavariable names
  , _names        :: Set Name -- top level names
  , _adtCtors     :: Map Name Lang.ADT
  } deriving Show

data ParseEnv = ParseEnv
  { _binders :: [Binder] -- binding contexts from lets, lambdas or foralls
  , _block   :: Set Name -- set of names in local `let` block
  } deriving Show

type Parser = RWST ParseEnv () ParseState (ParsecT Void Text Identity)

-- add top level name to state
names :: Name -> Parser ()
names n = do
  ds <- gets _names
  when (Set.member n reservedNames) (fail "reserved Name")
  when (Set.member n ds) (fail "attempted to redefine a name")
  modify (\s -> s {_names = Set.union (Set.singleton n) ds})
  where
    reservedNames =
      Set.fromList ["T", "enum", "case", "switch", "let", "when"]

-- add a list of binders to the context
binders :: [Binder] -> Parser a -> Parser a
binders bs p = local (\e -> e { _binders = (reverse bs) ++ _binders e }) p

-- add names to current mutual recursion block
block :: Name -> Parser a -> Parser a
block n p = do
  ds <- asks _block
  when (Set.member n ds) (fail "attempted to redefine a name")
  local (\e -> e { _block = Set.union (Set.singleton n) ds}) p

adtCtors :: Lang.ADT -> Parser ()
adtCtors a@(Lang.ADT _ _ _ m) = do
  cs <- gets _adtCtors
  modify (\s -> s {_adtCtors = M.union (const a <$> m) cs })

-- a parser is a Reader-Writer-State monad transformer wrapped over a ParsecT
-- TODO : Custom error messages

initParseState = ParseState 0 Set.empty M.empty
initParseEnv   = ParseEnv [] Set.empty

