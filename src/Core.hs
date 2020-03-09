module Core where

import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as M
import           Data.Set               (Set)
import qualified Data.Set               as Set
import           Data.Text              (Text)
import qualified Data.Text              as T
import           Prelude                hiding (floor)

import           Data.Bits              (complement, xor, (.&.), (.|.))
import qualified Data.Bits              as Bits
import qualified Data.ByteString        as B
import           Data.Word

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.RWS.Lazy hiding (All)
import           Control.Monad.State

import           IEEE754
import           Numeric.Extras
import           Numeric.IEEE

type Name = Text

data Eras = Eras  -- Erase from runtime
          | Keep  -- Keep at runtime
          deriving (Show, Eq, Ord)

-- Core.Term
data Term
  = Var Int                  -- Variable
  | Typ                      -- Type type
  | All Name Term Eras Term  -- Forall
  | Lam Name Term Eras Term  -- Lambda
  | App Term Term Eras       -- Application
  | Slf Name Term            -- Self-type
  | New Term Term            -- Self-type introduction
  | Use Term                 -- Self-type elimination
  | Dbl                      -- floating point number type
  | F64 Double               -- floating point value
  | Wrd                      -- integer number type
  | U64 Word64               -- integer value
  | Op1 Op FNum Term         -- Unary operation (curried)
  | Op2 Op Term Term         -- Binary operation
  | Ite Term Term Term       -- If-then-else
  | Ann Term Term            -- Type annotation
  | Log Term Term            -- inline log
  | Hol Name                 -- type hole or metavariable
  | Ref Name Cont            -- reference to a definition
  deriving (Eq, Show, Ord)

newtype Cont = Cont { _cont :: Term -> Term }

-- Cont is a continuation for correctin deBruijn index alignment when we
-- dereference. Since the only functions in here should
-- be `shift` and `subst` we could defunctionalize it with
--
-- | Ref Name [Cont]
--
-- data Cont = Shift Int Int | Subst Term Int
--
-- and then refunctionalize in `deref`

instance Eq Cont where
  a == b = True

instance Show Cont where
  show a = "_"

instance Ord Cont where
  compare a b = EQ


data FNum = W Word64 | D Double deriving (Show, Eq, Ord)

data Module = Module
  { _defs :: M.Map Name Term   -- Either top-level or local definitions
  } deriving (Eq, Show, Ord)

emptyModule :: Module
emptyModule = Module M.empty

-- shift DeBruijn indices by an increment above a depth in a term
shift :: Int -> Int -> Term -> Term
shift inc dep term = let go x = shift inc dep x in case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  All n h e b  -> All n (go h) e (shift inc (dep + 1) b)
  Lam n h e b  -> Lam n (go h) e (shift inc (dep + 1) b)
  App f a e    -> App (go f) (go a) e
  Slf n t      -> Slf n (shift inc (dep + 1) t)
  New t x      -> New (go t) (go x)
  Use x        -> Use (go x)
  Op1 o a b    -> Op1 o a (go b)
  Op2 o a b    -> Op2 o (go a) (go b)
  Ite c t f    -> Ite (go c) (go t) (go f)
  Ann t x      -> Ann (go t) (go x)
  Log m x      -> Log (go m) (go x)
  Ref n f      -> Ref n (Cont $ shift inc dep . _cont f)
  x            -> x

-- substitute a value for an index at a certain depth in a term
subst :: Term -> Int -> Term -> Term
subst v dep term =
  let v'   = shift 1 0 v
      go x = subst v dep x
  in
  case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  All n h e b -> All n (go h) e (subst v' (dep + 1) b)
  Lam n h e b -> Lam n (go h) e (subst v' (dep + 1) b)
  App f a e   -> App (go f) (go a) e
  Slf n t     -> Slf n (subst v' (dep + 1) t)
  New t x     -> New (go t) (go x)
  Use x       -> Use (go x)
  Op1 o a b   -> Op1 o a (go b)
  Op2 o a b   -> Op2 o (go a) (go b)
  Ite c t f   -> Ite (go c) (go t) (go f)
  Ann t x     -> Ann (go t) (go x)
  Log m x     -> Log (go m) (go x)
  Ref n f     -> Ref n (Cont $ subst v dep . _cont f)
  x           -> x

substMany :: Term -> [Term] -> Int -> Term
substMany t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i = go (subst (shift (l - i) 0 v) (d + l - i) t) vs d (i + 1)
    go t [] d i = t

deref :: Name -> Cont -> Module -> Term
deref n f defs = maybe (Ref n f) (_cont f) (M.lookup n (_defs defs))

-- deBruijn
eval :: Term -> Module -> Term
eval term mod = go term
  where
  go :: Term -> Term
  go t = case t of
    All n h e b -> All n h e b
    Lam n h e b -> Lam n h e (go b)
    App f a e   -> case go f of
        Lam n h e b  -> go (subst a 0 b)
        f            -> App f (go a) e
    New t x      -> go x
    Use x        -> go x
    Op1 o a b    -> case go b of
        U64 n -> op o a (W n)
        F64 n -> op o a (D n)
        x     -> Op1 o a x
    Op2 o a b   -> case go a of
        U64 n -> go (Op1 o (W n) b)
        F64 n -> go (Op1 o (D n) b)
        x     -> Op2 o x b
    Ite c t f   -> case go c of
        U64 n -> if n > 0 then go t else go f
        x     -> Ite x t f
    Ann t x     -> go x
    Log m x     -> Log (go m) (go x)
    Ref n f     -> case (deref n f mod) of
      Ref n f -> go (deref n f mod)
      x       -> go x
    _           -> t

-- for debugging
debug_eval :: Term -> Module -> IO Term
debug_eval term mod = go "top" term
  where
  go :: String -> Term -> IO Term
  go n t = do
    putStrLn $ n ++ " START: " ++ show t
    t' <- go_inner t
    putStrLn $ n ++ " END"
    return t'

  go_inner :: Term -> IO Term
  go_inner t = case t of
    All n h e b -> return $ All n h e b
    Lam n h e b -> Lam n h e <$> (go "Lam" b)
    App f a e   -> do
      f <- go "App" f
      case f of
        Lam n h e b  -> do
          (putStrLn $ "substituting " ++ show b ++ " <- " ++ show a) 
          go "Subst" (subst a 0 b)
        f            -> App f <$> (go "noLamArg" a) <*> return e
    New t x      -> go "New" x 
    Use x        -> go "Use" x
    Op1 o a b    -> do
      b <- go "Op1.b" b
      case b of
        U64 n -> return $ op o a (W n)
        F64 n -> return $ op o a (D n)
        x     -> return $ Op1 o a x
    Op2 o a b   -> do
      a <- go "Op2.a" a
      case a of
        U64 n -> go "Op2.b" (Op1 o (W n) b)
        F64 n -> go "Op2.b" (Op1 o (D n) b)
        x     -> return $ Op2 o x b
    Ite c t f   -> do
      c <- go "Ite.c" c
      case c of
        U64 n -> if n > 0 then go "Ite.t" t else go "Ite.f" f
        x     -> return $ Ite x t f
    Ann t x     -> go "Ann" x
    Log m x     -> Log <$> (go "Log.m" m) <*> (go "Log.x" x)
    Ref n f     -> do
      putStrLn $ show t
      case (deref n f mod) of
        Ref n f -> go "derefAgain" (deref n f mod)
        x       -> do
          (putStrLn $ "Dereferencing " ++ T.unpack n ++ " <- " ++ show x)
          (go "Deref" x)
    _           -> return $ t

erase :: Term -> Term
erase term = case term of
  All n h e b    -> All n (erase h) e (erase b)
  Lam n h Eras b -> erase $ subst (Hol "#erased") 0 b
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
  _              -> term

data Op
  = ADD  | SUB  | MUL  | DIV  | MOD  | EQL  | GTH  | LTH
  | AND  | BOR  | XOR  | NOT  | SHR  | SHL  | ROR  | ROL
  | MAX  | MIN  | POW  | CLZ  | CTZ  | CNT  | UTOF | FTOU
  | EXP  | EXPM | LOGB | LOGP | SQRT | CBRT | HYPT | ERF
  | FLOR | CEIL | NRST | NAN  | INF  | TRNC | CONV | COPY
  | SIN  | COS  | TAN  | ASIN | ACOS | ATAN
  | SINH | COSH | TANH | ASNH | ACSH | ATNH
  deriving (Eq, Show, Ord)


-- A general principle with `op` is that we should avoid making the
-- implementation (in this case Haskell) runtime error. i.e. all the primitive
-- Formality operations should be total and we should rely on type-safe
-- user-level librarys for partial functions like division. DIV is not division,
-- it is division extended with the points DIV(x,0) = 0.
--
-- See https://www.hillelwayne.com/post/divide-by-zero/ for further discussion
-- of whether this choice is reasonable

-- TODO: Find and eliminate other possible runtime errors in this function

op :: Op -> FNum -> FNum -> Term
op op a b
  | ADD  <- op, W a <- a, W b <- b = U64 $ a + b
  | ADD  <- op, D a <- a, D b <- b = F64 $ a + b
  | SUB  <- op, W a <- a, W b <- b = U64 $ a - b
  | SUB  <- op, D a <- a, D b <- b = F64 $ a - b
  | MUL  <- op, W a <- a, W b <- b = U64 $ a * b
  | MUL  <- op, D a <- a, D b <- b = F64 $ a * b
  | DIV  <- op, W a <- a, W 0 <- b = U64 $ 0
  | DIV  <- op, W a <- a, W b <- b = U64 $ a `div` b
  | DIV  <- op, D a <- a, D b <- b = F64 $ a / b
  | MOD  <- op, W a <- a, W b <- b = U64 $ a `mod` b
  | MOD  <- op, D a <- a, D b <- b = F64 $ a `fmod` b
  | EQL  <- op, W a <- a, W b <- b = U64 $ if a == b then 1 else 0
  | EQL  <- op, D a <- a, D b <- b = U64 $ if a == b then 1 else 0
  | GTH  <- op, W a <- a, W b <- b = U64 $ if a > b  then 1 else 0
  | GTH  <- op, D a <- a, D b <- b = U64 $ if a > b  then 1 else 0
  | LTH  <- op, W a <- a, W b <- b = U64 $ if a < b  then 1 else 0
  | LTH  <- op, D a <- a, D b <- b = U64 $ if a < b  then 1 else 0
  | MIN  <- op, W a <- a, W b <- b = U64 $ a `min` b
  | MIN  <- op, D a <- a, D b <- b = F64 $ a `minNaN` b
  | MAX  <- op, W a <- a, W b <- b = U64 $ a `max` b
  | MAX  <- op, D a <- a, D b <- b = F64 $ a `maxNaN` b
  | POW  <- op, W a <- a, W b <- b = U64 $ a ^ b
  | POW  <- op, D a <- a, D b <- b = F64 $ a ** b
  | AND  <- op, W a <- a, W b <- b = U64 $ a .&. b
  | BOR  <- op, W a <- a, W b <- b = U64 $ a .|. b
  | XOR  <- op, W a <- a, W b <- b = U64 $ a `xor` b
  | NOT  <- op, W b <- b           = U64 $ complement b
  | SHR  <- op, W a <- a, W b <- b = U64 $ Bits.shiftR b (fromIntegral a)
  | SHL  <- op, W a <- a, W b <- b = U64 $ Bits.shiftL b (fromIntegral a)
  | ROR  <- op, W a <- a, W b <- b = U64 $ Bits.rotateR b (fromIntegral a)
  | ROL  <- op, W a <- a, W b <- b = U64 $ Bits.rotateL b (fromIntegral a)
  | CLZ  <- op, W b <- b           = U64 $ cst $ Bits.countLeadingZeros b
  | CTZ  <- op, W b <- b           = U64 $ cst $ Bits.countTrailingZeros b
  | CNT  <- op, W b <- b           = U64 $ cst $ Bits.popCount b
  | SQRT <- op, D b <- b           = F64 $ sqrt b
  | NAN  <- op, D b <- b           = U64 $ if isNaN b then 1 else 0
  | INF  <- op, D b <- b           = U64 $ if isInfinite b then 1 else 0
  | COPY <- op, D a <- a, D b <- b = F64 $ copySign a b
  | EXP  <- op, D b <- b           = F64 $ exp b
  | EXPM <- op, D b <- b           = F64 $ expm1 b
  | LOGB <- op, D a <- a, D b <- b = F64 $ logBase a b
  | LOGP <- op, D b <- b           = F64 $ log1p b
  | SIN  <- op, D b <- b           = F64 $ sin b
  | COS  <- op, D b <- b           = F64 $ cos b
  | TAN  <- op, D b <- b           = F64 $ tan b
  | ASIN <- op, D b <- b           = F64 $ asin b
  | ACOS <- op, D b <- b           = F64 $ acos b
  | ATAN <- op, D b <- b           = F64 $ atan b
  | SINH <- op, D b <- b           = F64 $ sinh b
  | COSH <- op, D b <- b           = F64 $ cosh b
  | TANH <- op, D b <- b           = F64 $ tanh b
  | ASNH <- op, D b <- b           = F64 $ asinh b
  | ACSH <- op, D b <- b           = F64 $ acosh b
  | ATNH <- op, D b <- b           = F64 $ atanh b
  | CBRT <- op, D b <- b           = F64 $ cbrt b
  | HYPT <- op, D a <- a, D b <- b = F64 $ hypot a b
  | ERF  <- op, D b <- b           = F64 $ erf b
  | NRST <- op, D b <- b           = U64 $ round b
  | CEIL <- op, D b <- b           = F64 $ ceil b
  | FLOR <- op, D b <- b           = F64 $ floor b
  | TRNC <- op, D b <- b           = F64 $ trunc b
  | CONV <- op, W b <- b           = F64 $ fromIntegral b
  | UTOF <- op, W b <- b           = F64 $ utof b
  | FTOU <- op, D b <- b           = U64 $ ftou b
  | otherwise = error $ "UndefinedArithmetic Op"
    -- the only error op should raise is when there's an (OP, FNum, FNum)
    -- combination outside of this set. This is a language implementation error
    -- and should be impossible to generate from user-space
  where
    cst = fromIntegral
