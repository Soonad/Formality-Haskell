module Equality where

import qualified Data.Map.Strict     as M
import qualified Data.Sequence       as Seq
import           Data.Equivalence.Monad
import           Core

-- First-order Term
data FTerm
  = FVar Int
  | FTyp
  | FAll Int Name FTerm Eras FTerm
  | FLam Int Name FTerm Eras FTerm
  | FApp Int FTerm FTerm Eras
  | FSlf Int Name FTerm
  | FNew Int FTerm FTerm
  | FUse Int FTerm
  | FLet Int Name FTerm Recr FTerm
  | FNum
  | FVal Int
  | FOp1 Int Op Int FTerm
  | FOp2 Int Op FTerm FTerm
  | FIte Int FTerm FTerm FTerm
  | FAnn FTerm FTerm
  | FLog FTerm FTerm
  | FHol Name
  | FRef Name Int
  deriving (Eq, Show, Ord)


-- First order encoding
encode :: Term -> Defs -> FTerm
encode term defs = go term
  where
  go :: Term -> FTerm
  go term = case term of
    Var i       -> FVar i
    Typ         -> FTyp
    All n h e b -> FAll max n (go h) e (go $ subst b (Var $ max + 1) 0)
    Lam n h e b -> FLam max n (go h) e (go $ subst b (Var $ max + 1) 0)
    App f a e   -> FApp max (go f) (go a) e
    Slf n t     -> FSlf max n (go $ subst t (Var $ max + 1) 0)
    New t x     -> FNew max (go t) (go x)
    Use x       -> FUse max (go x)
    Let n t r b -> FLet max n (go t) r (go b)
    Num         -> FNum
    Val i       -> FVal i
    Op1 o a b   -> FOp1 max o a (go b)
    Op2 o a b   -> FOp2 max o (go a) (go b)
    Ite c t f   -> FIte max (go c) (go t) (go f)
    Ann t x     -> FAnn (go t) (go x)
    Log m x     -> FLog (go m) (go x)
    Hol n       -> FHol n
    Ref n i     -> FRef n i
  max = maxFreeVar term


forall n = All n Typ Keep
impl a b = All "" a Keep (shift b 1 0)

test1 :: Term
test1 =
  Let "X" (impl (Var 0) $ forall "b" $ impl (Var 0) (Ref "X" 0)) Equi
    (forall "a" $ (Ref "X" 0))

test2 :: Term
test2 =
  Let "X" (forall "a" $ impl (forall "c" $ impl (Var 1) (Var 0)) $ 
           forall "b" $ impl (Var 0) (Ref "X" 0)
          ) Equi
    (Ref "X" 0)

-- Equality algorithm
--data Node a = Leaf | Continue a | Branch a a
--
--sameNode :: FTerm -> Term -> Maybe (Node (Term, Term))
--sameNode (Ref n) s                   = sameNode (unroll' t) s
--sameNode t s@(Mu' _)                 = sameNode t (unroll' s)
--sameNode (All' i h b) (All' j h' b') = if i == j then Just $ Branch (h, h') (b, b') else Nothing
--sameNode (Lam' i h b) (Lam' j h' b') = if i == j then Just $ Branch (h, h') (b, b') else Nothing
--sameNode (App' i f a) (App' j f' a') = if i == j then Just $ Branch (f, f') (a, a') else Nothing
--sameNode (Slf' i t) (Slf' j t')      = if i == j then Just $ Continue (t, t') else Nothing
--sameNode (Var' i) (Var' j)           = if i == j then Just Leaf else Nothing
--sameNode (Rec' i) (Rec' j)           = if i == j then Just Leaf else Nothing
--sameNode (Val' i) (Val' j)           = if i == j then Just Leaf else Nothing
--sameNode Any' Any'                   = Just Leaf
--sameNode Typ' Typ'                   = Just Leaf
--sameNode Num' Num'                   = Just Leaf
--sameNode _ _                         = Nothing

