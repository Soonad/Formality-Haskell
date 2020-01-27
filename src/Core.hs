module Core where

import qualified Data.Map.Strict as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

type Name = Text
data Eras = Eras | Keep deriving (Show, Eq, Ord)
data Recr = Equi | Norm deriving (Show, Eq, Ord)

data Term
  = Var Int
  | Typ
  | All Name Term Eras Term
  | Lam Name Term Eras Term
  | App Term Term Eras
  | Slf Name Term
  | New Term Term
  | Use Term
  | Let Name Term Recr Term
  | Num
  | Val Int
  | Op1 Op Int Term
  | Op2 Op Term Term
  | Ite Term Term Term
  | Ann Term Term
  | Log Term Term
  | Hol Name
  | Ref Name Int
  deriving (Eq, Show, Ord)

data Op = ADD | SUB | MUL | DIV | MOD | EQL
-- | POW | AND | BOR | XOR | NOT | SHR | SHL | GTH | LTH | EQL
  deriving (Eq, Show, Ord)

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
  Let n t r b  -> Let n (go t) r (go b)
  Num          -> Num
  Val n        -> Val n
  Op1 o a b    -> Op1 o a (go b)
  Op2 o a b    -> Op2 o (go a) (go b)
  Ite c t f    -> Ite (go c) (go t) (go f)
  Ann t x      -> Ann (go t) (go x)
  Log m x      -> Log (go m) (go x)
  Hol n        -> Hol n
  Ref n i      -> Ref n i

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
  Let n t r b -> Let n (go t) r (go b)
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

type Defs = M.Map Name [(Recr, Term)]

defLookup :: Name -> Int -> Defs -> Maybe (Recr,Term)
defLookup n i defs = case M.lookup n defs of
  Just xs -> if i >= 0 && i < length xs then Just $ xs !! i else Nothing
  Nothing -> Nothing

dereference :: Name -> Int -> Defs -> Term
dereference n i defs = case M.lookup n defs of
  Just xs -> if i >= 0 && i < length xs then snd (xs !! i) else Ref n i
  Nothing -> Ref n i

hasFreeVar :: Term -> Defs -> Bool
hasFreeVar term defs = go term 0
  where
    go term n = case term of
      Var i        -> i == n
      All _ h _ b  -> go h n || go b (n + 1)
      Lam _ h _ b  -> go h n || go b (n + 1)
      App f a _    -> go f n || go a n
      Slf _ t      -> go t (n + 1)
      New t x      -> go t n || go x n
      Use x        -> go x n
      Let _ t r b  -> go t n || go b n
      Op1 o a b    -> go b n
      Op2 o a b    -> go a n || go b n
      Ite c t f    -> go c n || go t n || go f n
      Ann t x      -> go t n || go x n
      Log m x      -> go m n || go x n
      Ref n i      -> case dereference n i defs of
        Ref n i    -> False
        x          -> go x 0
      _            -> False

maxFreeVar :: Term -> Int
maxFreeVar term = go term 0
  where
    go term n = case term of
      Var i        -> if i < n then 0 else i-n
      All _ h _ b  -> go h n `max` go b (n + 1)
      Lam _ h _ b  -> go h n `max` go b (n + 1)
      App f a _    -> go f n `max` go a n
      Slf _ t      -> go t (n + 1)
      New t x      -> go t n `max` go x n
      Use x        -> go x n
      Let _ t r b  -> go t n `max` go b n
      Op1 o a b    -> go b n
      Op2 o a b    -> go a n `max` go b n
      Ite c t f    -> go c n `max` go t n `max` go f n
      Ann t x      -> go t n `max` go x n
      Log m x      -> go m n `max` go x n
      _            -> 0

extendDefs :: Name -> Term -> Recr -> Defs -> Defs
extendDefs n t r defs = M.insertWith ((++)) n [(r,t)] defs

-- deBruijn
eval :: Term -> Defs -> Term
eval term defs = go term defs
  where
  go :: Term -> Defs -> Term
  go t defs = case t of
    All n h e b -> All n h e b
    Lam n h e b -> Lam n h e (go b defs)
    App f a e   -> case (go f defs) of
      Lam n h e b  -> go (subst b a 0) defs
      f            -> App f (go a defs) e
    New t x      -> go x defs
    Use x        -> go x defs
    Let n t r b  -> go b (extendDefs n t r defs)
    Op1 o a b    -> case go b defs of
      Val n -> Val $ op o a n
      x     -> Op1 o a x
    Op2 o a b   -> case go a defs of
      Val n -> go (Op1 o n b) defs
      x     -> Op2 o x b
    Ite c t f   -> case go c defs of
      Val n -> if n > 0 then go t defs else go f defs
      x     -> Ite x t f
    Ann t x     -> go x defs
    Log m x     -> Log (go m defs) (go x defs)
    Ref n i      -> case (dereference n i defs) of
      Ref n' i'  -> if n' == n && i == i' then Ref n i
                    else go (dereference n' i' defs) defs
      x          -> go x defs
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

