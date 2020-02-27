module Lang where

import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M

import Data.Word

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
  | Cse Term [(Term, Term)] [(Name, Term)] (Maybe Term) -- Case-statement
  | Rwt Term Term                -- Rewrite
  | Wrd                          -- U64 Number type
  | Dbl                          -- F64 Number Type
  | U64 Word64                   -- U64 number value
  | F64 Double                   -- F64 number value
  | Opr Op Term Term             -- Binary operation
  | Ite Term Term Term           -- If-then-else
  | Ann Term Term                -- Type annotation
  | Log Term Term                -- inline log
  | Hol Name                     -- type hole or metavariable
  | Ref Name Int                 -- reference to a definition
  | Str Text                     -- String literal
  | Chr Char                     -- Character literal
  | Nat Bool Int                 -- Natural number literal
  | Bit Bool Integer             -- Bitstring literal
  | Par Term Term                -- Pair literal
  | Lst [Term]
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
