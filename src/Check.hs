module Check where

import           Prelude              hiding (log)

import qualified Data.Map.Strict      as M
import           Data.Maybe
import           Data.Set             (Set)
import qualified Data.Set             as Set
import           Data.Text            (Text)
import qualified Data.Text            as T

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS    hiding (All)
import           Control.Monad.State

import           Core

erase :: Term -> Term
erase term = case term of
  All n h e b    -> All n (erase h) e (erase b)
  Lam n h Eras b -> erase $ subst b (Hol "#erased") 0
  Lam n h e b    -> Lam n (erase h) e (erase b)
  App f a Eras   -> erase f
  App f a e      -> App (erase f) (erase a) e
  Op1 o a b      -> Op1 o a (erase b)
  Op2 o a b      -> Op2 o (erase a) (erase b)
  Ite c t f      -> Ite (erase c) (erase t) (erase f)
  Slf n t        -> Slf n (erase t)
  New t x        -> erase x
  Use x          -> erase x
  Ann t x        -> erase x
  Log m x        -> Log (erase m) (erase x)
  _ -> term

data CheckEnv = CheckEnv
  { _defs     :: Defs
  , _context  :: [Binder]
  , _erased   :: Eras
  } deriving (Show, Eq, Ord)

data Binder = Binder
  { _name :: Name
  , _type :: Term
  , _eras :: Eras
  } deriving (Show, Eq, Ord)

--instance Show Binder where
--  show (Binder n t Eras) = concat [T.unpack n, ":", show t, ";"]
--  show (Binder n t e) = concat [T.unpack n, ":", show t]

data CheckLog = CheckLog
  { _logs        :: [(Term, Term, [Binder])]
  , _constraints :: Set Constraint
  } deriving Show

instance Semigroup CheckLog where
  (<>) (CheckLog l c) (CheckLog l' c') = CheckLog (l <> l') (c <> c')

instance Monoid CheckLog where
  mappend = (<>)
  mempty = CheckLog mempty mempty

type Constraint = (CheckEnv, Term, Term)

data CheckState = CheckState
  { _holCount  :: Int
  , _refTypes  :: M.Map Name Term
  --, _eholCount :: Int
  } deriving Show

data CheckError
  = ErasedInKeptPosition Name
  | UnboundVariable Int CheckEnv
  | NotInScope Term
  | ErasureMismatch Term
  | UndefinedReference Name
  deriving Show

type Check = ExceptT CheckError (RWS CheckEnv CheckLog CheckState)

binder :: (Name,Term,Eras) -> Check a -> Check a
binder (n,h,e) = local (extend (Binder n h e))

erased :: Check Term -> Check Term
erased = local (\env -> env { _erased = Eras})

writeLog :: (Term, Term, [Binder]) -> Check ()
writeLog l = tell $ CheckLog (pure l) Set.empty

constrain :: (Term,Term) -> Check ()
constrain (x,y) = do
  e <- ask
  let c = (e,x,y)
  tell $ CheckLog [] (Set.singleton c)

expect :: Term -> Term -> Check Term
expect t x = do xT <- check x; constrain (t,xT); return xT

newHole :: Check Term
newHole= do
  c <- gets _holCount
  modify (\s -> s {_holCount = c + 1})
  return $ Hol (T.pack $ "#c" ++ show c)

--newEHol :: Check Eras
--newEHol= do
--  c <- gets _eholCount
--  modify (\s -> s {_eholCount = c + 1})
--  return $ EHol (T.pack $ "#e" ++ show c)

extend :: Binder -> CheckEnv -> CheckEnv
extend c env = env { _context = c : (_context env) }

check :: Term -> Check Term
check term = case term of
  Var i -> do
    ctx <- asks _context
    eras <- asks _erased
    when (i < 0 || i >= length ctx) (ask >>= (throwError . UnboundVariable i))
    let (Binder n t e) = ctx !! i
    when (e == Eras && eras == Keep) (throwError $ ErasedInKeptPosition n)
    return $ (shift t (i + 1) 0)
  Typ   -> return Typ
  All name from e to -> do
    erased $ expect Typ from
    erased $ binder (name,from,e) $ expect Typ to
    return Typ
  Lam name from eras body -> do
    e <- asks _erased
    erased $ expect Typ from
    to <- erased $ binder (name,from,eras) $ check body
    let typ = All name from eras to
    erased $ check typ
    return $ typ
  App fun arg e -> do
    funType <- local (\env -> env {_erased = e}) $ check fun
    argType <- check arg
    case funType of
      All _ from e' to -> do
        when (e /= e') (throwError $ ErasureMismatch term)
        constrain (from, argType)
        return (subst to arg 0)
      _               -> do
        (h1,h2) <- (,) <$> newHole <*> newHole
        e1      <- asks _erased
        constrain (funType, All "_" h1 e (App h2 (Var 0) e1))
        constrain (argType, h1)
        return $ App h2 arg e1
  Slf n t -> binder (n, Slf n t, Keep) (expect Typ t)
  New t x -> do
    h <- newHole
    tT <- expect (Slf "_" h) t
    xT <- expect (subst h (Ann t (New t x)) 0) x
    return t
  Use x -> do
    h  <- newHole
    xT <- expect (Slf "_" h) x
    return (subst h x 0)
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
    ctx <- asks _context
    writeLog (m, eval (erase mT) ds, ctx)
    check x
  Hol n -> return $ Hol (n `T.append` "_type")
  Ref n -> do
    ds <- asks _defs
    rs <- gets _refTypes
    case (ds M.!? n, rs M.!? n) of
      (Just t, Just tT) -> return tT
      (Just t, Nothing) -> do
        tT <- check t
        modify (\s -> s { _refTypes = M.insert n tT rs })
        return tT
      (Nothing, _) -> throwError $ UndefinedReference n
  Ann t x -> expect t x

runCheck :: CheckEnv -> CheckState -> Check a -> (Either CheckError a, CheckState, CheckLog)
runCheck env cs = (\x -> runRWS x env cs) . runExceptT

checkTerm :: Term -> (Either CheckError Term, CheckState, CheckLog)
checkTerm = (runCheck (CheckEnv M.empty [] Keep) (CheckState 0 M.empty)) . check

checkTermWithDefs :: M.Map Name Term -> Term -> (Either CheckError Term, CheckState, CheckLog)
checkTermWithDefs defs = (runCheck (CheckEnv defs [] Keep) (CheckState 0 M.empty)) . check

