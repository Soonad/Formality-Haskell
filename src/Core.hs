module Core where

import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as M
import           Data.Set               (Set)
import qualified Data.Set               as Set
import           Data.Text              (Text)
import qualified Data.Text              as T

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS.Lazy hiding (All)
import           Control.Monad.State

type Name = Text

data Eras = Eras  -- Erase from runtime
          | Keep  -- Keep at runtime
          deriving (Show, Eq, Ord)

-- Core.Term
data Term
  = Var Int                    -- Variable
  | Typ                        -- Type type
  | All Name Term Eras Term    -- Forall
  | Lam Name Term Eras Term    -- Lambda
  | App Term Term Eras         -- Application
  | Slf Name Term              -- Self-type
  | New Term Term              -- Self-type introduction
  | Use Term                   -- Self-type elimination
  | Num                        -- Number type
  | Val Int                    -- Number Value
  | Op1 Op Int Term            -- Unary operation (curried)
  | Op2 Op Term Term           -- Binary operation
  | Ite Term Term Term         -- If-then-else
  | Ann Term Term              -- Type annotation
  | Log Term Term              -- inline log
  | Hol Name                   -- type hole or metavariable
  | Ref Name Int               -- reference to a definition
  deriving (Eq, Show, Ord)

data Module = Module
  { _terms :: M.Map Int Term
  , _names :: M.Map Name Int
  } deriving (Eq, Show, Ord)

emptyModule :: Module
emptyModule = Module M.empty M.empty

data Op = ADD | SUB | MUL | DIV | MOD | EQL
-- | POW | AND | BOR | XOR | NOT | SHR | SHL | GTH | LTH | EQL
  deriving (Eq, Show, Ord)

-- shift DeBruijn indices in term by an increment at/greater than a depth
shift :: Term -> Int -> Int -> Term
shift term inc dep = let go x = shift x inc dep in case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  Typ          -> Typ
  All n h e b  -> All n (go h) e (shift b inc (dep + 1))
  Lam n h e b  -> Lam n (go h) e (shift b inc (dep + 1))
  App f a e    -> App (go f) (go a) e
  Slf n t      -> Slf n (shift t inc (dep + 1))
  New t x      -> New (go t) (go x)
  Use x        -> Use (go x)
  -- Let bs t     -> Let (go <$> bs) (go t)
  Num          -> Num
  Val n        -> Val n
  Op1 o a b    -> Op1 o a (go b)
  Op2 o a b    -> Op2 o (go a) (go b)
  Ite c t f    -> Ite (go c) (go t) (go f)
  Ann t x      -> Ann (go t) (go x)
  Log m x      -> Log (go m) (go x)
  Hol n        -> Hol n
  Ref n i      -> Ref n i

-- substitute a value for an index at a certain depth
subst :: Term -> Term -> Int -> Term
subst term v dep =
  let v'   = shift v 1 0
      go x = subst x v dep
  in
  case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  Typ         -> Typ
  All n h e b -> All n (go h) e (subst b v' (dep + 1))
  Lam n h e b -> Lam n (go h) e (subst b v' (dep + 1))
  App f a e   -> App (go f) (go a) e
  Slf n t     -> Slf n (subst t v' (dep + 1))
  New t x     -> New (go t) (go x)
  Use x       -> Use (go x)
  -- Let bs t    -> Let (go <$> bs) (go t)
  Num         -> Num
  Val n       -> Val n
  Op1 o a b   -> Op1 o a (go b)
  Op2 o a b   -> Op2 o (go a) (go b)
  Ite c t f   -> Ite (go c) (go t) (go f)
  Ann t x     -> Ann (go t) (go x)
  Log m x     -> Log (go m) (go x)
  Hol n       -> Hol n
  Ref n i     -> Ref n i

substMany :: Term -> [Term] -> Int -> Term
substMany t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i = go (subst t (shift v (l - i) 0) (d + l - i)) vs d (i + 1)
    go t [] d i = t

dereference :: Name -> Int -> Module -> Term
dereference n i defs = maybe (Ref n i) id (M.lookup i (_terms defs))

-- deBruijn
eval :: Term -> Module -> Term
eval term mod = go term
  where
  go :: Term -> Module -> Term
  go t mod = case t of
    All n h e b -> All n h e b
    Lam n h e b -> Lam n h e (go b)
    App f a e   -> case (go f) of
      Lam n h e b  -> go (subst b a 0) 
      f            -> App f (go a) e
    New t x      -> go x 
    Use x        -> go x 
    Op1 o a b    -> case go b  of
      Val n -> Val $ op o a n
      x     -> Op1 o a x
    Op2 o a b   -> case go a  of
      Val n -> go (Op1 o n b) 
      x     -> Op2 o x b
    Ite c t f   -> case go c  of
      Val n -> if n > 0 then go t  else go f 
      x     -> Ite x t f
    Ann t x     -> go x 
    Log m x     -> Log (go m) (go x)
    Ref n i      -> case (dereference n i mod) of
      Ref n' i'  -> if n' == n && i == i' then Ref n i
                    else go (dereference n' i' mod)
      x          -> go x
    _           -> t

op :: Op -> Int -> Int -> Int
op o a b = case o of
  ADD -> a + b
  SUB -> a - b
  MUL -> a * b
  DIV -> a `div` b
  MOD -> a `mod` b
  EQL -> if a == b then 1 else 0
  --POW -> a ^ b

erase :: Term -> Term
erase term = case term of
  All n h e b    -> All n (erase h) e (erase b)
  Lam n h Eras b -> erase $ subst b (Hol "#erased") 0
  Lam n h e b    -> Lam n (erase h) e (erase b)
  App f a Eras   -> erase f
  App f a e      -> App (erase f) (erase a) e
  Op1 o a b      -> Op1 o a (erase b)
  Op2 o a b      -> Op2 o (erase a) (erase b)
  Ite c t f      -> Ite (erase c) (erase t) (erase f)
  Slf n t        -> Slf n (erase t)
  New t x        -> erase x
  Use x          -> erase x
  -- Let bs t       -> Let (erase <$> bs) (erase t)
  Ann t x        -> erase x
  Log m x        -> Log (erase m) (erase x)
  _              -> term
