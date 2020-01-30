module Equality where

import qualified Data.Map.Strict     as M
import qualified Data.Sequence       as Seq
import           Data.Equivalence.Monad

import           Control.Monad.RWS.Lazy hiding (All)
import           Control.Monad.State

import           Core

type FBind = [(Name, Int, FTerm)]

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
  | FLet Int FBind FTerm
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


--type Encode = RWS EncodeEnv () EncodeState (Int,FTerm)
--
--data EncodeEnv = EncodeEnv { _dep :: Int, _defs :: Defs  }
--data EncodeState = EncodeState
--
---- First order encoding
--encode :: Term -> Defs -> (Int, FTerm)
--encode term defs = fst $ evalRWS (go term) (EncodeEnv 0 defs) EncodeState
--  where
--
--    go :: Term -> Encode
--    go term = case term of
--      Var idx       -> do
--        i <- asks _dep
--        return (if idx < i then 0 else idx - i,FVar i)
--      Typ         -> return (0, FTyp)
--      All n h e b -> do
--        (x, h') <- go h
--        (y, b') <- go b
--        let m = max x y
--        return (m, FAll m n h' e (subst b' (FVar $ m + 1) 0))
--      Lam n h e b -> do
--        (x, h') <- go h
--        (y, b') <- go b
--        let m = max x y
--        return (m, FLam m n h' e (subst b' (FVar $ m + 1) 0))
--
--maxFreeVar :: Term -> Int
--maxFreeVar term = go term 0 where
--  go term n = case term of
--    Var i        -> if i < n then 0 else i-n
--    All _ h e b  -> go h n `max` go b (n + 1)
--    Lam _ h e b  -> go h n `max` go b (n + 1)
--    App f a e    -> go f n `max` go a n
--    Slf _ t      -> go t (n + 1)
--    _            -> 0
--
---- First order encoding
--encode' :: Term -> Defs -> FTerm
--encode' term defs = go term
--  where
--  go :: Term -> FTerm
--  go term = case term of
--    Var i       -> FVar i
--    Typ         -> FTyp
--    All n h e b -> FAll max n (go h) e (go $ subst b (Var $ max + 1) 0)
--    Lam n h e b -> FLam max n (go h) e (go $ subst b (Var $ max + 1) 0)
--    App f a e   -> FApp max (go f) (go a) e
--    Slf n t     -> FSlf max n (go $ subst t (Var $ max + 1) 0)
--    New t x     -> FNew max (go t) (go x)
--    Use x       -> FUse max (go x)
--    Num         -> FNum
--    Val i       -> FVal i
--    Op1 o a b   -> FOp1 max o a (go b)
--    Op2 o a b   -> FOp2 max o (go a) (go b)
--    Ite c t f   -> FIte max (go c) (go t) (go f)
--    Ann t x     -> FAnn (go t) (go x)
--    Log m x     -> FLog (go m) (go x)
--    Hol n       -> FHol n
--    Ref n i     -> FRef n i
--  max = maxFreeVar term
--
--
--forall n = All n Typ Keep
--impl a b = All "" a Keep (shift b 1 0)
--
--test1 :: Term
--test1 = Let "X" (impl (Var 0) $ forall "b" $ impl (Var 0) (Ref "X" 0)) Equi
--    (forall "a" $ (Ref "X" 0))
--
--test2 :: Term
--test2 = Let "X" (forall "a" $ impl (forall "c" $ impl (Var 1) (Var 0)) $ 
--                 forall "b" $ impl (Var 0) (Ref "X" 0)
--                ) Equi
--        (Ref "X" 0)
--
--test3 = Let "X" (impl (Var 0) $ impl (Var 0) $ impl (Var 0) (Ref "X" 0)) Equi
--  (forall "a" $ (Ref "X" 0))
--test4 = Let "X" (impl (Var 0) $ impl (Var 0) (Ref "X" 0)) Equi
--  (forall "a" $ (Ref "X" 0))
--
---- Equality algorithm
--data Node a = Leaf | Continue a | Branch a a
--
--sameNode :: FTerm -> FTerm -> Maybe (Node (FTerm, FTerm))
--sameNode x y = go x y M.empty
--  where 
--    go t@(FRef n i) s d = go (encode (dereference n i d)) s d
--    go t s@(FRef n i) d = go t (encode (dereference n i d)) d
--    go (FAll i n h e b) (FAll j m h' e' b') d =
--      if i == j then Just $ Branch (h,h') (b,b') else Nothing
--    go (FLam i n h e b) (FLam j m h' e' b') d =
--      if i == j then Just $ Branch (h,h') (b,b') else Nothing
--    go (FSlf i n t) (FSlf j m t') d =
--      if i == j then Just $ Continue (t,t') else Nothing
--
----sameNode (Var' i) (Var' j)           = if i == j then Just Leaf else Nothing
----sameNode (Rec' i) (Rec' j)           = if i == j then Just Leaf else Nothing
----sameNode (Val' i) (Val' j)           = if i == j then Just Leaf else Nothing
----sameNode Any' Any'                   = Just Leaf
----sameNode Typ' Typ'                   = Just Leaf
----sameNode Num' Num'                   = Just Leaf
----sameNode _ _                         = Nothing
--
