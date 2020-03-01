{-# LANGUAGE FlexibleContexts #-}
module Core where

import Control.Applicative (liftA2)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import           Data.Equivalence.Monad
import qualified Data.Map.Strict as M
import           Data.Sequence (Seq(..), (><))
import qualified Data.Sequence as S

import           Data.Text (Text)
import qualified Data.Text as T

type Name = Text
data Eras = Eras  -- Erase from runtime
          | Keep  -- Keep at runtime
          -- | EHol Name  -- Erasure metavariable (probably not needed)
          deriving (Show, Eq, Ord)

data Dir  = Lft | Rgt | Ctr deriving (Eq, Show, Ord)
type Path = Seq Dir

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
--  | Let Name Term Term         -- locally scoped definition
  | Ref Name                   -- reference to a globally scoped definition
  -- The following should only be used by the equality algorithm
  | Bound Path
  deriving (Eq, Show, Ord)

data Op
  = ADD | SUB | MUL | DIV | MOD
  -- | POW | AND | BOR | XOR | NOT | SHR | SHL | GTH | LTH | EQL
  deriving (Eq, Show, Ord)

-- shift DeBruijn indices in term by an increment at/greater than a depth
shift :: Term -> Int -> Int -> Term
shift term inc dep = case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  All n h e b  -> All n (shift h inc dep) e (shift b inc (dep + 1))
  Lam n h e b  -> Lam n (shift h inc dep) e (shift b inc (dep + 1))
  App f a e    -> App (shift f inc dep) (shift a inc dep) e
  Slf n t      -> Slf n (shift t inc (dep + 1))
  New t x      -> New (shift t inc dep) (shift x inc dep)
  Use x        -> Use (shift x inc dep)
  Op1 o a b    -> Op1 o a (shift b inc dep)
  Op2 o a b    -> Op2 o (shift a inc dep) (shift b inc dep)
  Ite c t f    -> Ite (shift c inc dep) (shift t inc dep) (shift f inc dep)
  Ann t x      -> Ann (shift t inc dep) (shift x inc dep)
  Log m x      -> Log (shift m inc dep) (shift x inc dep)
  _            -> term

-- substitute a value for an index at a certain depth
subst :: Term -> Term -> Int -> Term
subst term v dep =
  let v' = shift v 1 0 in
  case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  All n h e b -> All n (subst h v dep) e (subst b v' (dep + 1))
  Lam n h e b -> Lam n (subst h v dep) e (subst b v' (dep + 1))
  App f a e   -> App (subst f v dep) (subst a v dep) e
  Slf n t     -> Slf n (subst t v' (dep + 1))
  New t x     -> New (subst t v dep) (subst x v dep)
  Use x       -> Use (subst x v dep)
  Op1 o a b   -> Op1 o a (subst b v dep)
  Op2 o a b   -> Op2 o (subst a v dep) (subst b v dep)
  Ite c t f   -> Ite (subst c v dep) (subst t v dep) (subst f v dep)
  Ann t x     -> Ann (subst t v dep) (subst x v dep)
  Log m x     -> Log (subst m v dep) (subst x v dep)
  _           -> term

substMany :: Term -> [Term] -> Int -> Term
substMany t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i = go (subst t (shift v (l - i) 0) (d + l - i)) vs d (i + 1)
    go t [] d i = t

type Defs = M.Map Name Term

dereference :: Name -> Defs -> Term
dereference n defs = maybe (error ("Undefined reference " ++ T.unpack n)) (\x -> x) $ M.lookup n defs

-- deBruijn
eval :: Term -> Defs -> Term
eval term defs = case term of
  All n h e b -> All n h e b
  Lam n h e b -> Lam n h e (eval b defs)
  App f a e   -> case eval f defs of
    Lam n' h' e b'  -> eval (subst b' a 0) defs
    f               -> App f (eval a defs) e
  Slf n t     -> Slf n t
  New t x     -> eval x defs
  Use x       -> eval x defs
  Op1 o a b    -> case eval b defs of
    Val n -> Val $ op o a n
    x     -> Op1 o a x
  Op2 o a b   -> case eval a defs of
    Val n -> eval (Op1 o n b) defs
    x     -> Op2 o x b
  Ite c t f   -> case eval c defs of
    Val n -> if n > 0 then eval t defs else eval f defs
    x     -> Ite x (eval t defs) (eval f defs)
  Ann t x     -> eval x defs
  Log m x     -> Log (eval m defs) (eval x defs)
  Ref n       -> eval (dereference n defs) defs
  _           -> term

op :: Op -> Int -> Int -> Int
op o a b = case o of
  ADD -> a + b
  SUB -> a - b
  MUL -> a * b
  DIV -> a `div` b
  MOD -> a `mod` b
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
  Ann t x        -> erase x
  Log m x        -> Log (erase m) (erase x)
  _ -> term

headForm :: Defs -> Term -> Term
headForm defs term = case term of
  App f a e -> case headForm defs f of
               Lam _ _ _ b -> headForm defs (subst b a 0)
               f     -> App f a e
  Op1 o a b -> case headForm defs b of
    Val n -> Val $ op o a n
    x     -> Op1 o a x
  Op2 o a b -> case headForm defs a of
    Val n -> headForm defs (Op1 o n b)
    x     -> Op2 o x b
  Ite c t f -> case headForm defs c of
    Val n -> if n > 0 then headForm defs t else headForm defs f
    x     -> Ite x t f
  Ref name  -> headForm defs (dereference name defs)
  _         -> term

sameNode :: Term -> Term -> Path -> Seq (Term, Term, Path)
sameNode t1 t2 ps = case (t1, t2) of
  (App f a _, App f' a' _) ->
    S.fromList [(f, f', ps :|> Lft), (a, a', ps :|> Rgt)]
  (Lam _ _ _ b, Lam _ _ _ b') ->
    S.singleton (subst b (Bound ps) 0, subst b' (Bound ps) 0, ps :|> Rgt)
  (All _ h _ b, All _ h' _ b') ->
    S.fromList [(h, h', ps :|> Lft), (subst b (Bound ps) 0, subst b' (Bound ps) 0, ps :|> Rgt)]
  (Slf _ b, Slf _ b') ->
    S.singleton (subst b (Bound ps) 0, subst b' (Bound ps) 0, ps :|> Ctr)
  (New _ b, New _ b') ->
    S.singleton (b, b', ps :|> Rgt)
  (Use b, Use b') ->
    S.singleton (b, b', ps :|> Ctr)
  (Op1 op i b, Op1 op' i' b') ->
    if i /= i' || op /= op'
    then Empty
    else S.singleton (b, b', ps :|> Ctr)
  (Op2 op a b, Op2 op' a' b') ->
    if op /= op'
    then Empty
    else S.fromList [(a, a', ps :|> Lft), (b, b', ps :|> Rgt)]
  (Ite b t f, Ite b' t' f') ->
    S.fromList [(b, b', ps :|> Lft), (t, t', ps :|> Ctr), (f, b', ps :|> Rgt)]
  (Ann _ b, Ann _ b') ->
    S.singleton (b, b', ps :|> Rgt)
  (Log _ b, Log _ b') ->
    S.singleton (b, b', ps :|> Rgt)
  _ ->
    Empty

equivalentTerms term1 term2 = do
  e <- equivalent term1 term2
  if e
    then return True
    else
    case (term1, term2) of
      (Lam _ _ _ b, Lam _ _ _ b')  -> equivalentTerms b b'
      (App f a _, App f' a' _)     -> equivalentTerms f f' &&* equivalentTerms a a'
      (All _ h _ b, All _ h' _ b') -> equivalentTerms h h' &&* equivalentTerms b b'
      (Slf _ b, Slf _ b')          -> equivalentTerms b b'
      (New _ b, New _ b')          -> equivalentTerms b b'
      (Use b, Use b')              -> equivalentTerms b b'
      (Op1 op i b, Op1 op' i' b')  -> pure (op == op') &&* (pure (i == i') &&* equivalentTerms b b')
      (Op2 op a b, Op2 op' a' b')  -> pure (op == op') &&* (equivalentTerms a a' &&* equivalentTerms b b')
      (Ite b t f, Ite b' t' f')    -> equivalentTerms b b' &&* (equivalentTerms t t' &&* equivalentTerms f f')
      (Ann _ b, Ann _ b')          -> equivalentTerms b b'
      (Log _ b, Log _ b')          -> equivalentTerms b b'
      _                            -> return False
  where
    (&&*) = liftA2 (&&)

equal :: Defs -> Term -> Term -> Bool
equal defs term1 term2 = runEquivM' $ go (S.singleton (term1, term2, Empty)) where
  go Empty = return True
  go ((t1, t2, ps) :<| tris) = do
    let term1 = headForm defs t1
    let term2 = headForm defs t2
    equate t1 term1
    equate t2 term2
    b <- equivalentTerms term1 term2
    equate term1 term2
    if b
      then go tris
      else
      case sameNode term1 term2 ps of
        Empty -> return False
        tris' -> go (tris >< tris')
