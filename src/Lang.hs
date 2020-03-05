module Lang where

import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Text       (Text)
import qualified Data.Text       as T
import           Data.Word

import           Core            (Eras (..), Name, Op (..))
import qualified Core            as Core

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
  | Cse Term [(Name, Term, Term)] (Map Name Term) (Maybe Term) -- Case-statement
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
  | Ref Name Int Int             -- reference to a definition
  | Str Text                     -- String value
  | Chr Char                     -- Character value
  | Nat Bool Int                 -- Natural number value
  | Bit Bool Integer             -- Bitstring value
  | Par [Term]                   -- Pair value
  | PTy [Term]                   -- Pair type
  | Get Name Name Term Term      -- Pair projection
  | Lst [Term]                   -- List valu
  | Sig [(Maybe Name,Term)] Term -- Sigma type
  deriving (Eq, Show, Ord)

-- Lang.Declaration
-- Top-level definitions in a module
data Declaration
  = Expr Name Term
  | Enum (Maybe Name) [Name]
  | Data ADT
  | Impt Text Text
  deriving (Eq, Show, Ord)

type Param = (Name,Term)
type Index = (Name,Term)
data Ctor = Ctor
  { _ctorParams :: [Param]
  , _ctorType   :: (Maybe Term)
  } deriving (Eq, Show, Ord)

data ADT = ADT Name [Param] [Index] (M.Map Name Ctor) deriving (Eq, Show, Ord)

-- a PreModule is an unsynthesizedunchecked collection of declarations
type PreModule = [Declaration]
