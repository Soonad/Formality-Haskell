

type Name = String

data Term = Var Int | Ref Name Int deriving (Eq, Show)

data Binder = VarB Name | RefB Name deriving (Eq, Show)

deBind :: [Binder] -> Int -> Name -> Term
deBind bs carets nam = go bs carets 0 0
  where
    go (x:xs) caretsLeft varIndex refCount
     | VarB n <- x, n == nam, caretsLeft == 0 = Var varIndex
     | VarB n <- x, n == nam                  = go xs (caretsLeft - 1) (varIndex + 1) refCount
     | VarB n <- x, n /= nam                  = go xs caretsLeft (varIndex + 1) refCount
     | RefB n <- x, n == nam, caretsLeft == 0 = Ref nam refCount
     | RefB n <- x, n == nam                  = go xs (caretsLeft - 1) varIndex (refCount + 1)
     | otherwise                              = go xs caretsLeft varIndex refCount
    go [] caretsLeft varIndex refCount        = Ref nam (caretsLeft + refCount)
