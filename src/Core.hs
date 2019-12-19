module Core where

import qualified Data.Map.Strict as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T

type Name = Text
type Eras = Bool
type Done = Bool

data Term
  = Var Int
  | Typ
  | All Name Term Term Eras
  | Lam Name Term Term Eras
  | App Term Term Eras
  | Slf Name Term
  | New Term Term
  | Use Term
  | Num
  | Val Int
  | Op1 Op Int Term
  | Op2 Op Term Term
  | Ite Term Term Term
  | Ann Term Term Done
  | Log Term Term
  | Hol Name
  | Ref Name
  deriving (Eq, Show, Ord)

data Op
  = ADD | SUB | MUL | DIV | MOD
  -- | POW | AND | BOR | XOR | NOT | SHR | SHL | GTH | LTH | EQL
  deriving (Eq, Show, Ord)

shift :: Term -> Int -> Int -> Term
shift term inc dep = case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  Typ          -> Typ
  All n h b e  -> All n (shift h inc dep) (shift b inc (dep + 1)) e
  Lam n h b e  -> Lam n (shift h inc dep) (shift b inc (dep + 1)) e
  App f a e    -> App (shift f inc dep) (shift a inc dep) e
  Slf n t      -> Slf n (shift t inc (dep + 1))
  New t x      -> New (shift t inc dep) (shift x inc dep)
  Use x        -> Use (shift x inc dep)
  Num          -> Num
  Val n        -> Val n
  Op1 o a b    -> Op1 o a (shift b inc dep)
  Op2 o a b    -> Op2 o (shift a inc dep) (shift b inc dep)
  Ite c t f    -> Ite (shift c inc dep) (shift t inc dep) (shift f inc dep)
  Ann t x d    -> Ann (shift t inc dep) (shift x inc dep) d
  Log m x      -> Log (shift m inc dep) (shift x inc dep)
  Hol n        -> Hol n
  Ref n        -> Ref n

subst :: Term -> Term -> Int -> Term
subst term v dep =
  let v' = shift v 1 0 in
  case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  Typ         -> Typ
  All n h b e -> All n (subst h v dep) (subst b v' (dep + 1)) e
  Lam n h b e -> Lam n (subst h v dep) (subst b v' (dep + 1)) e
  App f a e   -> App (subst f v dep) (subst a v dep) e
  Slf n t     -> Slf n (subst t v' (dep + 1))
  New t x     -> New (subst t v dep) (subst x v dep)
  Use x       -> Use (subst x v dep)
  Num         -> Num
  Val n       -> Val n
  Op1 o a b   -> Op1 o a (subst b v dep)
  Op2 o a b   -> Op2 o (subst a v dep) (subst b v dep)
  Ite c t f   -> Ite (subst c v dep) (subst t v dep) (subst f v dep)
  Ann t x d   -> Ann (subst t v dep) (subst x v dep) d
  Log m x     -> Log (subst m v dep) (subst x v dep)
  Hol n       -> Hol n
  Ref n       -> Ref n

substMany :: Term -> [Term] -> Int -> Term
substMany t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i = go (subst t (shift v (l - i) 0) (d + l - i)) vs d (i + 1)
    go t [] d i = t

type Defs = M.Map Text Term

-- deBruijn
eval :: Term -> Defs -> Term
eval term defs = case term of
  Var i       -> Var i
  Typ         -> Typ
  All n h b e -> All n h b e
  Lam n h b e -> Lam n h (eval b defs) e
  App f a e   -> case eval f defs of
    Lam n' h' b' e' -> eval (subst b' a 0) defs
    f               -> App f (eval a defs) e
  Slf n t     -> Slf n t
  New t x     -> eval x defs
  Use x       -> eval x defs
  Num         -> Num
  Val n       -> Val n
  Op1 o a b    -> case eval b defs of
    Val n -> Val $ op o a n
    x     -> Op1 o a x
  Op2 o a b   -> case eval a defs of
    Val n -> eval (Op1 o n b) defs
    x     -> Op2 o x b
  Ite c t f   -> case eval c defs of
    Val n -> if n > 0 then eval t defs else eval f defs
    x     -> Ite x (eval t defs) (eval f defs)
  Ann t x d   -> eval t defs
  Log m x     -> Log (eval m defs) (eval x defs)
  Hol n       -> Hol n
  Ref n     -> maybe (Ref n) (\x -> eval x defs) $ M.lookup n defs

op :: Op -> Int -> Int -> Int
op o a b = case o of
  ADD -> a + b
  SUB -> a - b
  MUL -> a * b
  DIV -> a `div` b
  MOD -> a `mod` b
  --POW -> a ^ b


