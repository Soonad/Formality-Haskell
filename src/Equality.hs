{-# LANGUAGE FlexibleContexts #-}
module Equality where

import           Data.Text                  (Text)
import qualified Data.Text                  as T
import Data.Char(chr)

import Data.Equivalence.Monad
import SimplerCore

-- First order (recursive) terms
data Term'
  = Rec' Int
  | Var' Int
  | Lam' Int Term' Term'
  | App' Int Term' Term'
  | All' Int Term' Term'
  | Mu' Term'
  | Slf' Int Term'
  | Any'
  | Typ'
  | Val' Int
  | Num'
  deriving (Eq, Show, Ord)

shiftRec' :: Term' -> Int -> Int -> Term'
shiftRec' term' inc dep = case term' of
  Lam' i h b -> Lam' i (shiftRec' h inc dep) (shiftRec' b inc dep)
  All' i h b -> All' i (shiftRec' h inc dep) (shiftRec' b inc dep)
  App' i f a -> App' i (shiftRec' f inc dep) (shiftRec' a inc dep)
  Mu'  t     -> Mu'  (shiftRec' t inc (dep + 1))
  Slf' i t   -> Slf' i (shiftRec' t inc dep)
  Rec' i     -> Rec' (if i < dep then i else (i + inc))
  _          -> term'

substRec' :: Term' -> Term' -> Int -> Term'
substRec' term' v dep = case term' of
  All' i h b   -> All' i (substRec' h v dep) (substRec' b v dep)
  Lam' i h b   -> Lam' i (substRec' h v dep) (substRec' b v dep)
  App' i f a   -> App' i (substRec' f v dep) (substRec' a v dep)
  Mu'  t       -> Mu'  (substRec' t vR (dep + 1))
  Slf' i t     -> Slf' i (substRec' t v dep)
  Rec' i       -> if i == dep then v else Rec' (i - if i > dep then 1 else 0)
  _            -> term'
  where
    vR = shiftRec' v 1 0

unroll' :: Term' -> Term'
unroll' term' = case term' of
  All' i h b -> All' i (unroll' h) (unroll' b)
  Lam' i h b -> Lam' i (unroll' h) (unroll' b)
  App' i f a -> App' i (unroll' f) (unroll' a)
  Mu'  t     -> substRec' t (Mu' t) 0
  Slf' i t   -> Slf' i (unroll' t)
  _          -> term'

-- Encoding of second order terms into first order terms
encode :: Term -> Term'
encode term = go term (\x -> x)
  where
  go :: Term -> (Term -> Term) -> Term'
  go term sigma = case term of
    Var i     -> Var' i
    Rec i     -> Rec' i
    All _ h b -> All' max (go h sigma) (go (substVar b (Var (max+1)) 0) sigma)
    Lam _ h b -> Lam' max (go h sigma) (go (substVar b (Var (max+1)) 0) sigma)
    App f a   -> App' max (go f sigma) (go a sigma)
    Mu  _ t   -> Mu'  (go t (\t -> sigma (substRec t (Var max) 0)))
    Slf _ t   -> Slf' max (go (substVar t (Var (max+1)) 0) sigma)
    Any       -> Any'
    Typ       -> Typ'
    Num       -> Num'
    Val i     -> Val' i
    where max = maxFreeVar (sigma term)

alphabet :: Int -> Text
alphabet x = T.pack $ reverse (go x)
  where go x = chr (rest+97) : (if div <= 0 then "" else go (div-1)) where (div, rest) = divMod x 26

toVar :: Int -> [Int] -> Int
toVar i lams = go i lams 0 where
  go i [] depth = i + depth
  go i (m : lams) depth = if m < i then depth else go i lams (depth + 1)

decode :: Term' -> Term
decode term' = go term' 0 []
  where
  go term' count lams = case term' of
    Var' i     -> Var (toVar i lams)
    All' m h b -> All (alphabet count) (go h count lams) (go b (count+1) (m : lams))
    Lam' m h b -> Lam (alphabet count) (go h count lams) (go b (count+1) (m : lams))
    App' m f a -> App (go f count lams) (go a count lams)
    Mu'  t     -> Mu  (alphabet count) (go t (count+1) lams)
    Slf' m t   -> Slf (alphabet count) (go t (count+1) (m : lams))
    Rec' i     -> Rec i
    Any'       -> Any
    Typ'       -> Typ
    Num'       -> Num
    Val' i     -> Val i

-- Equality algorithm
data Node' a = Stop' | Leaf' | Continue' a | Branch' a a

sameNode' :: Term' -> Term' -> Node' (Term', Term')
sameNode' t@(Mu' _) s                 = sameNode' (unroll' t) s
sameNode' t s@(Mu' _)                 = sameNode' t (unroll' s)
sameNode' (All' i h b) (All' j h' b') = if i == j then Branch' (h, h') (b, b') else Stop'
sameNode' (Lam' i h b) (Lam' j h' b') = if i == j then Branch' (h, h') (b, b') else Stop'
sameNode' (App' i f a) (App' j f' a') = if i == j then Branch' (f, f') (a, a') else Stop'
sameNode' (Slf' i t) (Slf' j t')      = if i == j then Continue' (t, t') else Stop'
sameNode' (Var' i) (Var' j)           = if i == j then Leaf' else Stop'
sameNode' (Rec' i) (Rec' j)           = if i == j then Leaf' else Stop'
sameNode' (Val' i) (Val' j)           = if i == j then Leaf' else Stop'
sameNode' Any' Any'                   = Leaf'
sameNode' Typ' Typ'                   = Leaf'
sameNode' Num' Num'                   = Leaf'
sameNode' _ _                         = Stop'

-- Syntactic equality of first order trees, ignores reduction
equalTerms' :: Term' -> Term' -> Bool
equalTerms' term1' term2' = runEquivM' $ go [(term1', term2')] where
  go [] = return True
  go ((term1, term2) : pairs) = case sameNode' term1 term2 of
    Branch' pair1 pair2 -> do
      b <- equivalent term1 term2
      if b
        then go pairs
        else equate term1 term2 >> go (pair1 : pair2 : pairs)
    Continue' pair -> do
      b <- equivalent term1 term2
      if b
        then go pairs
        else equate term1 term2 >> go (pair : pairs)
    Leaf' -> equate term1 term2 >> go pairs
    Stop' -> return False

-- Equality of terms. A better `eval` function is needed, since we will also have recursive term-level functions
equalTerms :: Term -> Term -> Bool
equalTerms term1 term2 = equalTerms' (encode (eval term1)) (encode (eval term2))

-- Tests
test1 = forall "a" $ Mu "X" $ impl (Var 0) $ forall "b" $ impl (Var 0) (Rec 0)
test2 = Mu "X" $ forall "a" $ impl (forall "c" $ impl (Var 1) (Var 0)) $ forall "b" $ impl (Var 0) (Rec 0)

-- Equal terms
test3 = forall "a" $ Mu "X" $ impl (Var 0) $ impl (Var 0) $ impl (Var 0) (Rec 0)
test4 = forall "a" $ Mu "X" $ impl (Var 0) $ impl (Var 0) (Rec 0)

-- the type `Unit` and its constructor `unit`, referred to here as unitType and unitTerm respectively, is defined by the system of equations
-- unitType = unitTypeConstructor unitType unitTerm
-- unitTerm = unitTermConstructor unitType unitTerm
-- where
unitTypeConstructor t s = Slf "self" $ All "P" (impl t Typ) $ impl (App (Var 0) s) $ App (Var 0) (Var 1)
unitTermConstructor t s = Lam "P" (impl t Typ) $ Lam "x" (App (Var 0) s) (Var 0)

-- We can solve this with the terms
unitType = Mu "Unit" $ unitTypeConstructor (Rec 0) $ Mu "unit" $ unitTermConstructor (Rec 1) (Rec 0) -- ${self} (P: unitType -> Type;) -> P(unitTerm) -> P(self)
unitTerm = Mu "unit" $ unitTermConstructor unitType (Rec 0) -- (P: unitType -> Type; x: P(unitTerm)) => x

-- and check that indeed they solve the equations
unitTypeEq = equalTerms unitType (unitTypeConstructor unitType unitTerm)
unitTermEq = equalTerms unitTerm (unitTermConstructor unitType unitTerm)

-- In fact we are able to generalize this result to arbitrary mutual recursive definitions. However, as we see in the following example,
-- the solutions get exponentially bigger and more complex with an increase in the number of mutual recursive definitions.
boolConstructor  b t f = Slf "self" $ All "P" (impl b Typ) $ impl (App (Var 0) t) $ impl (App (Var 0) f) $ App (Var 0) (Var 1)
trueConstructor  b t f = Lam "P" (impl b Typ) $ Lam "case_true" (App (Var 0) t) $ Lam "case_false" (App (Var 1) f) (Var 1)
falseConstructor b t f = Lam "P" (impl b Typ) $ Lam "case_true" (App (Var 0) t) $ Lam "case_false" (App (Var 1) f) (Var 0)

bool  = Mu "Bool"  $ boolConstructor (Rec 0)
  (Mu "true"  $ trueConstructor  (Rec 1) (Rec 0) (Mu "false" $ falseConstructor (Rec 2) (Rec 1) (Rec 0)))
  (Mu "false" $ falseConstructor (Rec 1) (Mu "true"  $ trueConstructor  (Rec 2) (Rec 0) (Rec 1)) (Rec 0))
true  = Mu "True"  $ trueConstructor  bool (Rec 0) (Mu "false" $ falseConstructor bool (Rec 1) (Rec 0))
false = Mu "False" $ falseConstructor bool true (Rec 0)

boolEq  = equalTerms bool  (boolConstructor  bool true false)
trueEq  = equalTerms true  (trueConstructor  bool true false)
falseEq = equalTerms false (falseConstructor bool true false)
