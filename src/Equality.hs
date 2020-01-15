module Equality where

import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)

import Data.List (findIndex)

type Name = String

data Term
  = Var Int
  | Typ
  | Val Int
  | Num
  | Lam Name Term Term
  | App Term Term
  | All Name Term Term
  | Def Name Term
  | Rec Int
  | Ref Name
  deriving (Eq, Ord)

hasFreeVar :: Term -> Bool
hasFreeVar term = go term 0 
  where
    go term n = case term of
      Var i        -> i == n
      All _ h b    -> go h n || go b (n + 1)
      Lam _ h b    -> go h n || go b (n + 1)
      App f a      -> go f n || go a n
      Def _ t      -> go t n
      _            -> False

hasFreeRec :: Term -> Bool
hasFreeRec term = go term 0 
  where
    go term n = case term of
      All _ h b    -> go h n || go b n
      Lam _ h b    -> go h n || go b n
      App f a      -> go f n || go a n
      Def _ t      -> go t (n + 1)
      Rec i        -> i == n
      _            -> False

--newtype Pretty = Pretty { unpretty :: Term }

instance Show Term where
  show t = go t [] []
    where
      go :: Term -> [String] -> [String] -> String
      go t vs rs = case t of
        Var i          -> if i < length vs then vs !! i else concat ["^", show i]
        Typ            -> "Type"
        Num            -> "Number"
        All n h b      -> if hasFreeVar b
          then concat ["(", n, " : ", go h vs rs, ") -> ", go b (n : vs) rs]
          else concat [go h vs rs, " -> ", go b (n : vs) rs]
        Lam n h b      -> 
          concat ["(", n, " : ", go h vs rs, ") => ", go b (n : vs) rs]
        App f@(Lam _ _ _) a    ->
          concat ["((", go f vs rs, ") " , go a vs rs, ")"]
        App f a        -> concat ["(", go f vs rs, " ", go a vs rs, ")"]
        Def n t        -> concat ["def ", n, ". ", go t vs (n : rs)]
        Ref n          -> "_" ++ n
        Rec i          -> if i < length rs then rs !! i else concat ["^", show i]
        Val i          -> show i

shiftVar :: Term -> Int -> Int -> Term
shiftVar term inc dep = case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  All n h b    -> All n (shiftVar h inc dep) (shiftVar b inc (dep + 1))
  Lam n h b    -> Lam n (shiftVar h inc dep) (shiftVar b inc (dep + 1))
  App f a      -> App (shiftVar f inc dep) (shiftVar a inc dep)
  Def n t      -> Def n (shiftVar t inc dep)
  x            -> x

shiftRec :: Term -> Int -> Int -> Term
shiftRec term inc dep = case term of
  Lam n h b -> Lam n (shiftRec h inc dep) (shiftRec h inc dep)
  All n h b -> All n (shiftRec h inc dep) (shiftRec h inc dep)
  App f a   -> App (shiftRec f inc dep) (shiftRec a inc dep)
  Def n t   -> Def n (shiftRec t inc (dep + 1))
  Rec i     -> Rec (if i < dep then i else (i + inc))
  x         -> x

substVar :: Term -> Term -> Int -> Term
substVar term v dep = let v' = shiftVar v 1 0 in case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  All n h b   -> All n (substVar h v dep) (substVar b v' (dep + 1))
  Lam n h b   -> Lam n (substVar h v dep) (substVar b v' (dep + 1))
  App f a     -> App (substVar f v dep) (substVar a v dep)
  Def n t     -> Def n (substVar t v dep)
  x           -> x

substRec :: Term -> Term -> Int -> Term
substRec term v dep = let v' = shiftRec v 1 0 in case term of
  All n h b   -> All n (substRec h v dep) (substRec b v dep)
  Lam n h b   -> Lam n (substRec h v dep) (substRec b v' dep)
  App f a     -> App (substRec f v dep) (substRec a v dep)
  Def n t     -> Def n (substRec t v' (dep + 1))
  Rec i       -> if i == dep then v else Rec (i - if i > dep then 1 else 0)
  x           -> x

substManyVar :: Term -> [Term] -> Int -> Term
substManyVar t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i =
      go (substVar t (shiftVar v (l - i) 0) (d + l - i)) vs d (i + 1)
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
      Lam _ _ b' -> eval (substVar b' a' 0)
      f          -> App f a'
  Num       -> Num
  Val n     -> Val n
  Def n t   -> eval (substRec t (Def n t) 0)
  Rec i     -> Rec i
  Ref n     -> Ref n

deref :: Term -> M.Map String Term -> Term
deref term defs = go term []
  where 
    go t ctx = case t of
      Lam n h b -> Lam n (go h ctx) (go b ctx)
      All n h b -> All n (go h ctx) (go b ctx)
      App f a   -> App (go f ctx) (go a ctx)
      Def n t   -> Def n (go t (n:ctx))
      Ref n     -> case findIndex ((==) n) ctx of
        Just i  -> Rec i
        Nothing -> go (defs M.! n) ctx
      _         -> t

contractibleSubst :: Term -> Int -> Bool
contractibleSubst t n = case t of
  Rec i     -> i /= n
  Def _ t   -> contractibleSubst t (n + 1)
  Lam _ _ _ -> False
  App _ _   -> False
  _         -> True

-- The Lam and App cases could potentially be, instead
--  Lam _ t b -> contractibleSubst t n || contractibleSubst b (n + 1)
--  App f a   -> contractibleSubst f n || contractibleSubst a n
-- However, a contractible term T would lose the useful property that if it is normalized, then T^n is also normalized,
-- for any power n, where T^n means substitute variable 0 in T by itself n times, that is,
-- `T^0 = Var 0` and `T^(n+1) = subst T^n T 0`. This means in particular that if T is contractible,
-- then `Def "X" T` is normalized no matter how many times we unroll it.

-- Examples of substitutions which are not contractible when you consider evaluation of terms, which rule out `Lam` and `App` as guards for recursion
notcontractible1 = Def "X" (Lam "a" Typ (App (Rec 0) (Var 0)))
notcontractible2 = Def "X" (App (Lam "a" Typ (Var 0)) (Rec 0))

inf = Def "Inf" (All "_" Num (Rec 0))

inf2 = Def "Inf2" (All "_" Num (Rec 0))

f = Def "f" (All "_" Num (Ref "g"))
g = Def "g" (All "_" Num (Ref "f"))

fg_defs = M.fromList [("f",f),("g",g)]



