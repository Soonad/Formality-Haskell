module CoreSyn where

import           Data.List                  hiding (group)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (fromJust, isJust)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import           Control.Monad              (void)
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy     hiding (All)
import           Control.Monad.Except

import           Core hiding (_terms)
import qualified Lang as Lang

type Syn a = ExceptT SynError (RWS SynEnv () SynState) a

data SynState = SynState
  { _idCount :: ID
  , _terms   :: Map ID Term
  } deriving Show

newID :: Syn ID
newID = do
  i <- gets _idCount
  modify (\s -> s { _idCount = ID $ (unID $ _idCount s) + 1 })
  return $ i

data SynEnv = SynEnv
  { _refs :: Map Name [ID]
  } deriving Show

withNames :: Map Name ID -> Syn a -> Syn a
withNames ns p = 
  local (\e -> e { _refs = M.unionWith (++) (pure <$> ns) (_refs e)}) p


data SynError
  = UndefinedReference Name Int (Map Name [ID])
  deriving (Show, Eq)

syn :: Lang.Term -> Syn Term
syn term = case term of
  Lang.Var n        -> return $ Var n
  Lang.Typ          -> return $ Typ
  Lang.All n h e b  -> do h' <- syn h; All n h' e <$> (syn b)
  Lang.Lam n h e b  -> do h' <- syn h; Lam n h' e <$> (syn b)
  Lang.App f a e    -> do f' <- syn f; a' <- syn a; return $ App f' a' e
  Lang.Slf n t      -> Slf n <$> syn t
  Lang.New t x      -> do t' <- syn t; New t' <$> (syn x)
  Lang.Use x        -> Use <$> syn x
  Lang.Let ds t     -> do ns <- synBlock ds; withNames ns $ syn t
  Lang.Num          -> return $ Num
  Lang.Val n        -> return $ Val n
  Lang.Opr o a b    -> do a' <- syn a; b' <- syn b; return $ Op2 o a' b'
  Lang.Ite c t f    -> do c' <- syn c; t' <- syn t; Ite c' t' <$> (syn f)
  Lang.Ann t x      -> do t' <- syn t; Ann t' <$> (syn x)
  Lang.Log m x      -> do m' <- syn m; Log m' <$> (syn x)
  Lang.Hol n        -> return $ Hol n
  Lang.Ref n i      -> do
    rs <- asks _refs
    case refLookup n i rs of
      Just j  -> return $ Ref n j
      _       -> throwError $ UndefinedReference n i rs

synBlock :: Map Name Lang.Term -> Syn (Map Name ID)
synBlock ds = do
  i     <- gets _idCount
  names <- sequence $ (const newID) <$> ds
  j     <- gets _idCount
  let pre = M.fromList $ zip ([i..j]) (M.elems ds)
  terms <- withNames names $ traverse syn pre
  modify (\s -> s { _terms = M.union terms (_terms s) })
  return names


(!?) :: [a] -> Int -> Maybe a
(!?) xs i = if i >= 0 && i < length xs then Just $ xs !! i else Nothing
infixl 9 !?

refLookup :: Name -> Int -> Map Name [ID] -> Maybe ID
refLookup n i refs = M.lookup n refs >>= (\xs -> xs !? i)

runSyn :: SynEnv -> SynState -> Syn a -> (Either SynError a, SynState, ())
runSyn env ste = (\x -> runRWS x env ste) . runExceptT

defaultEnv   = SynEnv M.empty
defaultState = SynState (ID 0) M.empty

coreSyn :: Map Name Lang.Term -> Either SynError Core.Module
coreSyn ds = (\a -> Core.Module (_terms s) a) <$> a
  where
    (a,s,()) = runSyn defaultEnv defaultState (synBlock ds)


