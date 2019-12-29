module Core where

import qualified Data.Map.Strict as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

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

-- pretty-printing
pretty :: Term -> Text
pretty t = go t []
  where
    show' = T.pack . show
    cat   = T.concat

    showOp ADD = " + "
    showOp SUB = " - "
    showOp MUL = " * "
    showOp DIV = " / "
    showOp MOD = " % "

    go :: Term -> [Text] -> Text
    go t s = case t of
      Var i       -> if i < length s then s !! i else cat ["^", show' i]
      Typ         -> "Type"
      All n h b e -> cat ["(", n, " : ", go h s, ") -> ", go b (n : s)]
      Lam n h b e -> cat ["(", n, " : ", go h s, ") => ", go b (n : s)]
      App f a True  -> cat ["(", go f s, " " , go a s, ";)"]
      App f a False -> cat ["(", go f s, " ", go a s, ")"]
      Slf n t     -> cat ["${", n, "}", go t s]
      New t x     -> cat ["new(", go t s, ")", go x s]
      Use x       -> cat ["use(", go x s, ")"]
      Num         -> "Number"
      Val i       -> show' i
      Op2 o a b   -> cat [go a s, showOp o, go b s]
      Op1 o a b   -> cat [show' a, showOp o, go b s]
      Ite c t f   -> cat ["if ", go c s, " then ", go t s, " else ", go f s]
      Ann x y d   -> cat [go y s, " :: ", go x s]
      Log x y     -> cat ["log(", go x s, "); ", go y s]
      Hol n       -> cat ["?", n]
      Ref n       -> n

data IsEq = Eql Term Term | And IsEq IsEq | Or IsEq IsEq | Ret Bool

equal :: Term -> Term -> Defs -> Bool
equal a b defs = go (Eql a b)
  where
    go t = case t of
      Ret v -> v
      _ -> go (step t)

    step t = case t of
      Eql a b -> let
        ex = case (eval a M.empty, eval b M.empty) of
          (Ref aN, Ref bN) -> if aN == bN then Just (Ret True) else Nothing
          (App aF aA _, App bF bA _) -> Just (And (Eql aF bF) (Eql aA bA))
          _ -> Nothing
        ey = case (eval a defs, eval b defs) of
          (Var i, Var j) -> Ret $ i == j
          (Typ, Typ) -> Ret True
          (All _ aH aB _, All _ bH bB _) -> And (Eql aH bH) (Eql aB bB)
          (Lam _ aH aB _, Lam _ bH bB _) -> Eql aB bB
          (App aF aA _, App bF bA _)     -> And (Eql aF bF) (Eql aA bA)
          (Slf _ aT, Slf _ bT)           -> Eql aT bT
          (New _ aX, New _ bX)           -> Eql aX bX
          (Use aX, Use bX)               -> Eql aX bX
          (Num, Num)                     -> Ret True
          (Val i, Val j)                 -> Ret $ i == j
          (Op1 aO aX aY, Op1 bO bX bY)   ->
            if aO /= bO then Ret False else And (Ret $ aX == bX) (Eql aY bY)
          (Op2 aO aX aY, Op2 bO bX bY)   ->
            if aO /= bO then Ret False else And (Eql aX bX) (Eql aY bY)
          (Ite aC aT aF, Ite bC bT bF)   -> And (Eql aC bC) (Eql aT bT)
          (Ann aT aV _, Ann bT bV _)     -> Eql aV bV
          _                              -> Ret False
        in maybe ey (\x -> Or x ey) ex
      And (Ret False) _ -> Ret False
      And (Ret True) y  -> y
      And _ (Ret False) -> Ret False
      And x (Ret True)  -> x
      And x y  -> And (step x) (step y)
      Or (Ret True) y   -> Ret True
      Or (Ret False) y  -> y
      Or x (Ret True)   -> Ret True
      Or x (Ret False)  -> x
      Or x y            -> Or (step x) (step y)
      Ret v             -> Ret v


data Env = Env 
  { defs :: Defs
  , ctx :: [CtxElem]
  } deriving Show

data CtxElem = CtxElem
  { _name :: Name
  , _term :: Term
  --, _type :: Maybe Term
  --, _eras :: Bool
  } deriving Show

extend :: CtxElem -> Env -> Env
extend c env = env {ctx = c : (ctx env) }

inEnv :: (Name,Term) -> Check a -> Check a
inEnv (n,h) = local (extend (CtxElem n h))

getCtx :: Int -> Env -> Maybe CtxElem
getCtx i c
  | i < 0 || i >= (length $ ctx c) = Nothing
  | otherwise = case (ctx c) !! i of
    CtxElem n t -> Just $ CtxElem n (shift t (i + 1) 0)
    --CtxElem n t (Just ty) e ->
    --  Just $ CtxElem n (shift t (i + 1) 0) (Just $ shift ty (i + 1) 0) e

data TypeError
  = TypeMismatch Term Term Env
  | NonErasedPosition Name Term
  | UnboundVariable Env
  | NotFunction Term
  | NotInScope Term
  | LamIsntAll Term Term
  | AllIsntType Term Term
  | ErasureMismatch Term
  | Op1NotNum
  | Op2NotNum
  | IteNotOnNum
  | NewNotSlf
  | UseNotSlf
  deriving Show

type Check = ExceptT TypeError (Reader Env)

match :: Term -> Term -> Check ()
match a b = do
  d <- asks defs
  if equal a b d then return () else do
    e <- ask
    throwError $ TypeMismatch a b e

check :: Term -> Check Term
check term = case term of
  Var i -> do
    c <- asks (getCtx i)
    case c of
      Nothing -> do e <- ask; throwError $ UnboundVariable e
      Just c -> return $ _term c
  Typ   -> return Typ
  All n h b e -> do
    hT <- check h
    bT <- inEnv (n,h) (check b)
    match hT Typ
    match bT Typ >> return Typ
  Lam n h b e -> do
    bT <- inEnv (n,h) (check b)
    let t = All n h bT e
    check t >> return t
  App f a e -> do
    fT <- check f
    d <- asks defs
    case eval fT d of
      All fN fH fB _ -> do
        aT <- check a
        match aT fH >> return (subst fB (Ann fB a False) 0)
      _ -> throwError $ NotFunction f
  Slf n t -> do
    tT <- inEnv (n, Ann Typ (Slf n t) False) (check t)
    match tT Typ >> return Typ
  New t x -> do
    d <- asks defs
    let tT = eval t d
    case tT of
      Slf s sT -> do
        check tT
        tT <- check x
        match tT (subst sT (Ann tT (New sT x) False) 0) >> return sT
      _ -> throwError NewNotSlf
  Use x -> do
    xT <- check x
    d <- asks defs
    case eval xT d of
      (Slf s sT) -> return (subst sT x 0)
      _          -> throwError UseNotSlf
  Num   -> return Typ
  Val _ -> return Num
  Op1 o a b -> do
    bT <- check b
    match bT Num >> return Num
  Op2 o a b -> do
    aT <- check a
    match aT Num
    bT <- check b
    match bT Num >> return Num
  Ite c t f -> do
    cT <- check c
    match cT Num
    tT <- check t
    fT <- check f
    match tT fT >> return tT
  --Log
  --Hol
  Ref n -> do
    d <- asks defs
    return $ d M.! n
  Ann t x d -> do
    xT <- check x
    match t xT >> return t

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = (\x -> runReader x env) . runExceptT

