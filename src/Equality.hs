module Equality where

type Name = String
--data Eras = Eras
--          | Keep
--          -- | EHol Name
--          deriving (Show, Eq, Ord)

data Term
  = Var Int
  | Typ
  | Val Int
  | Num
  | Lam Name Term Term --  | Lam Name Term Eras Term
  | App Term Term --  | App Term Term Eras
  | All Name Term Term --  | All Name Term Eras Term
  | Rec Name Term
--  | Slf Name Term
--  | New Term Term
--  | Use Term
--  | Op1 Op Int Term
--  | Op2 Op Term Term
--  | Ite Term Term Term
--  | Ann Term Term
--  | Log Term Term
--  | Hol Name
--  | Ref Name
  deriving (Eq, Ord)

instance Show Term where
  show t = go t []
    where
      go :: Term -> [String] -> String
      go t s = case t of
        Var i          -> if i < length s then s !! i else concat ["^", show i]
        Typ            -> "Type"
        All n h b      -> concat ["(", n, " : ", go h s, ") -> ", go b (n : s)]
        Lam n h b      -> concat ["(", n, " : ", go h s, ") => ", go b (n : s)]
        App f@(Lam _ _ _) a    ->
          concat ["((", go f s, ") " , go a s, ")"]
        App f@(Rec _ _) a    ->
          concat ["((", go f s, ") " , go a s, ")"]
        App f a        -> concat ["(", go f s, " ", go a s, ")"]
        Rec n t        -> concat ["rec ", n, ". ", go t (n : s)]
        Num            -> "Number"
        Val i          -> show i

shift :: Term -> Int -> Int -> Term
shift term inc dep = case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  Typ          -> Typ
  All n h b    -> All n (shift h inc dep) (shift b inc (dep + 1))
  Lam n h b    -> Lam n (shift h inc dep) (shift b inc (dep + 1))
  App f a      -> App (shift f inc dep) (shift a inc dep)
  Num          -> Num
  Val n        -> Val n
  Rec n t      -> Rec n (shift t inc (dep + 1))

subst :: Term -> Term -> Int -> Term
subst term v dep =
  let v' = shift v 1 0 in
  case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  Typ         -> Typ
  All n h b   -> All n (subst h v dep) (subst b v' (dep + 1))
  Lam n h b   -> Lam n (subst h v dep) (subst b v' (dep + 1))
  App f a     -> App (subst f v dep) (subst a v dep)
  Num         -> Num
  Val n       -> Val n
  Rec n t     -> Rec n (subst t v' (dep + 1))

substMany :: Term -> [Term] -> Int -> Term
substMany t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i = go (subst t (shift v (l - i) 0) (d + l - i)) vs d (i + 1)
    go t [] d i = t

eval :: Term -> Term
eval term = case term of
  Var i     -> Var i
  Typ       -> Typ
  All n h b -> All n (eval h) (eval b)
  Lam n h b -> Lam n (eval h) (eval b)
  App f a   ->
    let a' = eval a
    in case eval f of
      Lam _ _ b' -> eval (subst b' a' 0)
      f            -> App f a'
  Num       -> Num
  Val n     -> Val n
  Rec n t   -> Rec n (eval t)

unroll :: Term -> Term
unroll term = case term of
  Var i     -> Var i
  Typ       -> Typ
  All n h b -> All n h (unroll b)
  Lam n h b -> Lam n (unroll h) (unroll b)
  App f a   -> App (unroll f) (unroll a)
  Num       -> Num
  Val n     -> Val n
  Rec n t   -> subst t (Rec n t) 0
