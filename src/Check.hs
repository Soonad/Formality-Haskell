module Check where

import qualified Data.Map.Strict as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import Data.Maybe

import Control.Monad.Reader
import Control.Monad.RWS hiding (All)
import Control.Monad.State
import Control.Monad.Except

import Core

data IsEq = Eql Term Term | And IsEq IsEq | Or IsEq IsEq | Ret Bool

erase :: Term -> Term
erase term = case term of
  All n h b e     -> All n (erase h) (erase b) e
  Lam n h b True  -> erase $ subst b (Hol "#erased") 0
  Lam n h b False -> Lam n (erase h) (erase b) False
  App f a True    -> erase f
  App f a False   -> App (erase f) (erase a) False
  Op1 o a b       -> Op1 o a (erase b)
  Op2 o a b       -> Op2 o (erase a) (erase b)
  Ite c t f       -> Ite (erase c) (erase t) (erase f)
  Slf n t         -> Slf n (erase t)
  New t x         -> erase x
  Use x           -> erase x
  Ann t x         -> erase x
  Log m x         -> Log (erase m) (erase x)
  _ -> term

--data EqualEnv = EqualEnv
--  { 

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
          (Ann aT aV, Ann bT bV)         -> Eql aV bV
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
  { _defs     :: Defs
  , _ctx      :: [CtxElem]
  , _expect   :: Maybe Term
  , _erasable :: Bool
  } deriving Show

data CtxElem = CtxElem
  { _name :: Name
  , _type :: Term
  , _eras :: Bool
  } deriving Show



extend :: CtxElem -> Env -> Env
extend c env = env { _ctx = c : (_ctx env) }

getCtx :: Int -> Env -> Maybe CtxElem
getCtx i c
  | i < 0 || i >= (length $ _ctx c) = Nothing
  | otherwise = case (_ctx c) !! i of
    CtxElem n t e -> Just $ CtxElem n (shift t (i + 1) 0) e

type Logs = [(Term, Term, [CtxElem])]

data CheckST = CheckST
  { _holes :: M.Map Name Term
  } deriving Show

data TypeError
  = TypeMismatch Term Term Env
  | NonErasedPosition Name
  | UnboundVariable Env
  | NotFunction Term
  | NotInScope Term
  | LamIsntAll Term
  | AllIsntType Term
  | ErasureMismatch Term
  | NewNotSlf Term Term
  | UseNotSlf Term Term
  deriving Show

type Check = ExceptT TypeError (RWS Env Logs CheckST)

match :: Term -> Term -> Check ()
match a b = do
  d <- asks _defs
  if equal a b d then return () else do
    e <- ask
    throwError $ TypeMismatch a b e

expect :: Term -> Term -> Check Term
expect t x = do
  xT <- local (\e -> e { _expect = Just t }) (check x)
  match xT t >> return xT

erasable :: Check Term -> Check Term
erasable = local (\e -> e { _erasable = True})

inEnv :: (Name,Term,Bool) -> Check a -> Check a
inEnv (n,h,e) = local (extend (CtxElem n h e))

check :: Term -> Check Term
check term = case term of
  Var i -> do
    c <- asks (getCtx i)
    case c of
      Just c -> do
        e <- asks _erasable
        if (_eras c) && not e then throwError $ NonErasedPosition (_name c)
          else return $ _type c
      Nothing -> do e <- ask; throwError $ UnboundVariable e
  Typ   -> return Typ
  All name ntyp btyp eras -> do
    expected <- asks _expect
    when (expected /= Just Typ && expected /= Nothing)
      (throwError $ AllIsntType (fromJust expected))
    erasable $ expect Typ ntyp
    erasable $ inEnv (name,ntyp,eras) (expect Typ btyp)
    return Typ
  Lam name ntyp body eras -> do
    expected <- asks _expect
    case expected of
      Just exp@(All n nT b e) -> do
        erasable $ expect Typ ntyp
        btyp <- inEnv (name,ntyp,eras) $ check body
        let typ = All name ntyp btyp eras
        erasable $ expect exp typ
        return typ
      Just x             -> throwError (LamIsntAll x)
      Nothing            -> do
        erasable $ expect Typ ntyp
        btyp <- inEnv (name,ntyp,eras) $ check body
        let typ = All name ntyp btyp eras
        erasable $ check typ
        return typ
  App f a e -> do
    fT <- check f
    d <- asks _defs
    case eval fT d of
      All fN fH fB fE -> do
        when (e /= fE) (throwError $ ErasureMismatch term)
        aT <- if e then erasable $ expect fH a else expect fH a
        return (subst fB (Ann fB a) 0)
      _ -> throwError $ NotFunction f
  Slf n t -> inEnv (n, Slf n t, False) (expect Typ t)
  New t x -> do
    d <- asks _defs
    let tT = eval t d
    case tT of
      Slf s sT -> do
        check tT
        expect (subst sT (Ann tT (New sT x)) 0) x
        return sT
      _ -> throwError $ NewNotSlf term tT
  Use x -> do
    xT <- check x
    d <- asks _defs
    case eval xT d of
      (Slf s sT) -> return (subst sT x 0)
      _          -> throwError $ UseNotSlf term xT
  Num   -> return Typ
  Val _ -> return Num
  Op1 o a b -> expect Num b
  Op2 o a b -> expect Num a >> expect Num b
  Ite c t f -> do
    cT <- expect Num c
    tT <- check t
    expect tT f
  -- Logs in Writer monad
  Log m x -> do
    mT  <- check m
    ds  <- asks _defs
    ctx <- asks _ctx
    tell [(m, eval (erase mT) ds, ctx)]
    check x
  -- Holes in State monad
  Hol n -> return $ Hol n
  Ref n -> do
    ds <- asks _defs
    return $ maybe (Ref n) (\x -> eval x ds) $ M.lookup n ds
  Ann t x -> expect t x

runCheck :: Env -> CheckST -> Check a -> (Either TypeError a, CheckST, Logs)
runCheck env cs = (\x -> runRWS x env cs) . runExceptT

checkTerm :: Term -> (Either TypeError Term, CheckST, Logs)
checkTerm = (runCheck (Env M.empty [] Nothing False) (CheckST M.empty)) . check

