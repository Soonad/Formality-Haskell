module Lang where

import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M

import qualified Data.ByteString as BS
import Data.ByteString (ByteString)
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import           Core                       (Eras (..), Name, Op (..))
import qualified Core                       as Core


-- Lang.Term
-- The Formality frontend language which includes syntax sugar
data Term
  = Var Int                      -- Variable
  | Typ                          -- Type type
  | All Name Term Eras Term      -- Forall
  | Lam Name Term Eras Term      -- Lambda
  | App Term Term Eras           -- Application
  | Slf Name Term                -- Self-type
  | New Term Term                -- Self-type introduction
  | Use Term                     -- Self-type elimination
  | Let (Map Name Term) Term     -- Recursive locally scoped definition
  | Whn [(Term, Term)] Term      -- When-statement
  | Swt Term [(Term,Term)] Term  -- Switch-statement
  | Cse Term [Term] [(Name, Term)] (Maybe Term) -- Case-statement
  | Rwt Term Term Term           -- Rewrite
  | Num                          -- Number type
  | Val Int                      -- Number Value
  | Opr Op Term Term             -- Binary operation
  | Ite Term Term Term           -- If-then-else
  | Ann Term Term                -- Type annotation
  | Log Term Term                -- inline log
  | Hol Name                     -- type hole or metavariable
  | Ref Name Int                 -- reference to a definition
  | Bit ByteString
  | IBits ByteString
  | Str Text
  | Nat Int
  | Pair Term Term
  deriving (Eq, Show, Ord)

-- Lang.Declaration
-- Top-level definitions in a module
data Declaration
  = Expr Name Term
  | Enum [Name]
  | Data Name [Param] [Index] [Ctor]
  | Impt Text Text
  deriving (Eq, Show, Ord)

type Param = (Name,Term)
type Index = (Name,Term)
data Ctor = Ctor Name [Param] (Maybe Term) deriving (Eq, Show, Ord)

-- a PreModule is an unsynthesized/unchecked collection of defintions
type PreModule = [Declaration]
