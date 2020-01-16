module FirstOrder where

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

encode :: Term -> (Term -> Term) -> Term'
encode term sigma = case term of
  Var i     -> Var' i
  Rec i     -> Rec' i
  All _ h b -> All' max (encode h sigma) (encode (substVar b (Var (max+1)) 0) sigma)
  Lam _ h b -> Lam' max (encode h sigma) (encode (substVar b (Var (max+1)) 0) sigma)
  App f t   -> App' max (encode f sigma) (encode t sigma)
  Mu n t    -> Mu'  n (encode t (\t -> sigma (substRec t (Var max) 0)))
  Any       -> Any'
  Typ       -> Typ'
  Num       -> Num'
  Val i     -> Val' i
  where max = maxFreeVar (sigma term)
