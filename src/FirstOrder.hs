module FirstOrder where

import Data.Char(chr)
import SimplerCore

data Term'
  = Rec' Int
  | Var' Int
  | Lam' Int Term' Term'
  | App' Int Term' Term'
  | All' Int Term' Term'
  | Mu' Name Term'
  | Any'
  | Typ'
  | Val' Int
  | Num'
  deriving (Eq, Show, Ord)

encode :: Term -> Term'
encode term = go term (\x -> x)
  where
  go :: Term -> (Term -> Term) -> Term'
  go term sigma = case term of
    Var i     -> Var' i
    Rec i     -> Rec' i
    All _ h b -> All' max (go h sigma) (go (substVar b (Var (max+1)) 0) sigma)
    Lam _ h b -> Lam' max (go h sigma) (go (substVar b (Var (max+1)) 0) sigma)
    App f t   -> App' max (go f sigma) (go t sigma)
    Mu  n t   -> Mu'  n (go t (\t -> sigma (substRec t (Var max) 0)))
    Any       -> Any'
    Typ       -> Typ'
    Num       -> Num'
    Val i     -> Val' i
    where max = maxFreeVar (sigma term)

alphabet :: Int -> String
alphabet x = reverse (go x)
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
    App' m f t -> App (go f count lams) (go t count lams)
    Mu'  n t   -> Mu  n (go t count lams)
    Rec' i     -> Rec i
    Any'       -> Any
    Typ'       -> Typ
    Num'       -> Num
    Val' i     -> Val i
  
-- Tests
forall n = All n Typ
impl a b = All "" a (shiftVar b 1 0)

test1 = forall "a" $ Mu "X" $ impl (Var 0) $ forall "b" $ impl (Var 0) (Rec 0)
test2 = Mu "X" $ forall "a" $ impl (forall "c" $ impl (Var 1) (Var 0)) $ forall "b" $ impl (Var 0) (Rec 0)
