module CoreSyn where

import           Data.List              hiding (group)
import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as M
import           Data.Maybe             (fromJust, isJust)
import           Data.Set               (Set)
import qualified Data.Set               as Set
import           Data.Text              (Text)
import qualified Data.Text              as T
import           Data.Void
import           Data.Char

import           Control.Monad          (void)
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy hiding (All)

import           Core                   hiding (_terms)
import qualified Lang                   as Lang

import qualified Parser                 as P

type Syn a = ExceptT SynError (RWS SynEnv () SynState) a

data SynState = SynState
  { _idCount :: Int
  , _terms   :: Map Name Term  -- All definitions
  } deriving Show

newName :: Name -> Syn Name
newName n = do
  i <- gets _idCount
  modify (\s -> s { _idCount = i + 1 })
  return $ T.concat ["$", n, T.pack (show i)]

data SynEnv = SynEnv
  { _refs :: Map Name [Name]
  } deriving Show

withNames :: Map Name Name -> Syn a -> Syn a
withNames ns p =
  local (\e -> e { _refs = M.unionWith (++) (pure <$> ns) (_refs e)}) p

data SynError
  = UndefinedReference Name Int Int (Map Name [Name])
  deriving (Show, Eq)

synTerm :: Lang.Term -> Syn Term
synTerm term = case term of
  Lang.Var n              -> return $ Var n
  Lang.Typ                -> return $ Typ
  Lang.All n h e b        -> All n <$> syn h <*> return e <*> syn b
  Lang.Lam n h e b        -> Lam n <$> syn h <*> return e <*> syn b
  Lang.App f a e          -> App <$> syn f <*> syn a <*> return e
  Lang.Slf n t            -> Slf n <$> syn t
  Lang.New t x            -> New <$> syn t <*> syn x
  Lang.Use x              -> Use <$> syn x
  Lang.Dbl                -> return Dbl
  Lang.F64 n              -> return $ F64 n
  Lang.Wrd                -> return Wrd
  Lang.U64 n              -> return $ U64 n
  Lang.Let ds t           -> do ns <- synBlock ds; withNames ns $ syn t
  Lang.Opr o a b          -> Op2 o <$> syn a <*> syn b
  Lang.Ite c t f          -> Ite <$> syn c <*> syn t <*> syn f
  Lang.Ann t x            -> Ann <$> syn t <*> syn x
  Lang.Log m x            -> Log <$> syn m <*> syn x
  Lang.Hol n              -> return $ Hol n
  Lang.Whn [(c,t)] e      -> Ite <$> syn c <*> syn t <*> syn e
  Lang.Whn ((c,t):cs) e   -> Ite <$> (syn c) <*> syn t <*> syn (Lang.Whn cs e)
  Lang.Swt m [(c,t)] e    -> Ite <$> (syn $ Lang.Opr EQL m c)
                                 <*> (syn t)
                                 <*> (syn e)
  Lang.Swt m ((c,t):cs) e -> Ite <$> (syn $ Lang.Opr EQL m c)
                                 <*> (syn t)
                                 <*> (syn $ Lang.Swt m cs e)
  --Lang.Cse m ws adt cs t  -> do
    

  Lang.Ref n i s     -> do
    rs <- asks _refs
    case refLookup n i rs of
      Just m  -> return $ Ref m (Cont $ shift s 0)
      _       -> throwError $ UndefinedReference n i s rs
  where
    syn = synTerm

synBlock :: Map Name Lang.Term -> Syn (Map Name Name)
synBlock ds = do
  i     <- gets _idCount
  names <- sequence $ M.mapWithKey (\k v -> newName k) ds
  j     <- gets _idCount
  let pre = M.mapKeys (\x -> names M.! x) ds
  terms <- withNames names $ traverse synTerm pre
  modify (\s -> s { _terms = M.union terms (_terms s) })
  return names

synModule :: [Lang.Declaration] -> Syn (Map Name Term)
synModule ds = M.fromList . concat <$> (traverse synDecl ds)
  where
    synDecl :: Lang.Declaration -> Syn [(Name,Term)]
    synDecl d = case d of
      --Lang.Impt -> do
      Lang.Expr n t -> do
        t <- synTerm t
        return $ [(n,t)]
      Lang.Enum n ns -> case n of
        Just n -> do
          let str = buildString n
          let enumTyp   = (n, Ann Typ (App (Ref "Enum" (Cont id)) str Eras))
          let enumVal x = App (App (Ref "enum" (Cont id)) str Keep) (U64 x) Keep
          let enumVals  = zip ns $ enumVal <$> [0..]
          return $ enumTyp : enumVals
        _ -> return $ zip ns $ U64 <$> [0..]

      --Lang.Data adt -> do

buildString :: Text -> Term
buildString txt = let
  str   = T.unpack txt
  nums  = (fromIntegral . ord) <$> str
  t     = App (Ref "nil" (Cont id)) Wrd Eras
  f a b = App (App (App (Ref "cons" (Cont id)) Wrd Eras) (U64 a) Keep) b Keep
  in foldr f t nums

refLookup :: Name -> Int -> Map Name [Name] -> Maybe Name
refLookup n i refs = M.lookup n refs >>= (\xs -> xs !? i)
  where
    (!?) :: [a] -> Int -> Maybe a
    (!?) xs i = if i >= 0 && i < length xs then Just $ xs !! i else Nothing

runSyn :: SynEnv -> SynState -> Syn a -> (Either SynError a, SynState, ())
runSyn env ste = (\x -> runRWS x env ste) . runExceptT

defaultEnv   = SynEnv M.empty
defaultState = SynState 0 M.empty

synDefault :: Syn a -> (Either SynError a, SynState, ())
synDefault s = runSyn defaultEnv defaultState s

coreSyn :: SynEnv -> SynState -> [Lang.Declaration] -> Either SynError Core.Module
coreSyn env ste ds = (\a -> Core.Module $ M.union a (_terms s)) <$> a
  where
    (a,s,()) = runSyn env ste (synModule ds)


