module Lang where

import           Prelude                    hiding (log)

import           Data.Char
import           Data.List                  hiding (group)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (fromJust, isJust)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import qualified Data.Text.IO               as TIO
import           Data.Void

import           Control.Monad              (void)
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy     hiding (All)

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Debug

import           Core                       (Eras (..), Name, Op (..))
import qualified Core                       as Core
import           Pretty

import qualified Data.ByteString as BS
import Data.ByteString (ByteString)

-- Lang.Term, this includes syntax sugars like `Let`
data Term
  = Var Int                      -- Variable
  | Typ                          -- Type type
  | All Name Term Eras Term      -- Forall
  | Lam Name Term Eras Term      -- Lambda
  | App Term Term Eras           -- Application
  | Slf Name Term                -- Self-type
  | New Term Term                -- Self-type introduction
  | Use Term                     -- Self-type elimination
  | Let (Map Name Term) Term     -- Recursive locally scoped definition
  | Whn [(Term, Term)] Term      -- When-statement
  | Swt Term [(Term,Term)] Term  -- Switch-statement
  | Cse Term [Term] [(Name, Term)] (Maybe Term) -- Case-statement
  | Rwt Term Term Term           -- Rewrite
  | Num                          -- Number type
  | Val Int                      -- Number Value
  | Opr Op Term Term             -- Binary operation
  | Ite Term Term Term           -- If-then-else
  | Ann Term Term                -- Type annotation
  | Log Term Term                -- inline log
  | Hol Name                     -- type hole or metavariable
  | Ref Name Int                 -- reference to a definition
  | Bits ByteString
  | IBits ByteString
  | String Text
  | Nat Int
  | Pair Term Term
  deriving (Eq, Show, Ord)

data Def
  = Expr Name Term
  | Enum [Name]
  | Data Name [Param] [Index] [Ctor]
  | Impt Text Text
  deriving (Eq, Show, Ord)

type Param = (Name,Term)
type Index = (Name,Term)
data Ctor = Ctor Name [Param] (Maybe Term) deriving (Eq, Show, Ord)

-- binders can bind variables (deBruijn) or references
data Binder = VarB Name | RefB Name deriving (Eq, Show)

data ParseState = ParseState
  { _holeCount    :: Int      -- for generating unique metavariable names
  , _names        :: Set Name -- top level names
  } deriving Show

data ParseEnv = ParseEnv
  { _binders :: [Binder] -- binding contexts from lets, lambdas or foralls
  , _block   :: Set Name -- set of names in local `let` block
  } deriving Show

-- add top 
names :: [Name] -> Parser ()
names ns = modify (\s -> s {_names = Set.union (Set.fromList ns) (_names s)})

-- add a list of binders to the context
binders :: [Binder] -> Parser a -> Parser a
binders bs p = local (\e -> e { _binders = (reverse bs) ++ _binders e }) p

-- add names to current mutual recursion block
block :: [Name] -> Parser a -> Parser a
block n p = local (\e -> e { _block = Set.union (Set.fromList n) (_block e)}) p

-- a parser is a Reader-Writer-State monad transformer wrapped over a ParsecT
-- TODO : Custom error messages
type Parser = RWST ParseEnv () ParseState (ParsecT Void Text Identity)

initParseState = ParseState 0 Set.empty
initParseEnv   = ParseEnv [] Set.empty

-- top level parser with default env and state
parseDefault :: Show a
             => Parser a
             -> Text
             -> Either (ParseErrorBundle Text Void) (a, ParseState, ())
parseDefault p s =
  runIdentity $ runParserT (runRWST p initParseEnv initParseState) "" s

-- a useful testing function
parserTest :: Show a => Parser a -> Text -> IO ()
parserTest p s = print $ parseDefault p s

fileTest :: Show a => Parser a -> FilePath -> IO ()
fileTest p f = do
  txt <- TIO.readFile f
  print $ parseDefault p txt

-- evals the term directly
--evalTest :: Parser Term -> Text -> IO ()
--evalTest p s = do
--  let Identity (Right (a,st,w)) = parseDefault p s
--  print $ a
--  print $ eval a Core.emptyModule

-- space consumer
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "//") empty

-- symbol followed by spaces
sym :: Text -> Parser Text
sym t = L.symbol sc t

-- symbol not followed by spaces
lit :: Text -> Parser Text
lit t = string t

name :: Parser Text
name = do
  us <- many (lit "_")
  n  <- if us == [] then letterChar else alphaNumChar
  ns <- many (alphaNumChar <|> satisfy (\x -> elem x nameSymbol))
  let nam = T.concat [T.concat us, T.pack (n : ns)]
  if nam `elem` reservedWords then fail "reservedWord" else return nam
  where
    nameSymbol :: [Char]
    nameSymbol = "_.-@/'"
    reservedWords :: [Text]
    reservedWords = ["let", "rewrite", "T", "case", "with"]

-- resolves if a name is a variable or reference
refVar :: Parser Term
refVar = do
  ctx <- asks _binders
  is <- optional (some (lit "^"))
  n <- name
  let carets = (maybe 0 id (length <$> is))
  return $ go ctx carets 0 0 n
  where
    go(x:xs) cs varIndex refCount n
      | VarB m <- x, n == m, cs == 0 = Var varIndex
      | VarB m <- x, n == m          = go xs (cs - 1) (varIndex + 1) refCount n
      | VarB m <- x, n /= m          = go xs cs (varIndex + 1) refCount n
      | RefB m <- x, n == m, cs == 0 = Ref n refCount
      | RefB m <- x, n == m          = go xs (cs - 1) varIndex (refCount + 1) n
      | otherwise                    = go xs cs varIndex refCount n
    go [] cs varIndex refCount n     = Ref n (cs + refCount)

-- numeric type
num :: Parser Term
num = lit "Number" >> return Num

-- numeric value
val :: Parser Term
val = Val <$> L.decimal

-- The type "Type"
typ :: Parser Term
typ = lit "Type" >> return Typ

-- forall or lambda
allLam :: Parser Term
allLam = do
  bs <- binds True "(" ")"
  sc
  ctor <- (sym "->" >> return All) <|> (sym "=>" >> return Lam)
  sc
  body <- binders ((\(x,y,z) -> VarB x) <$> bs) group'
  return $ foldr (\(n,t,e) x -> ctor n t e x) body bs

-- binders in a forall or lambda
binds :: Bool -> Text -> Text -> Parser [(Name, Term, Eras)]
binds erasable start end = sym start >> go
  where
    go = (sc >> lit end >> return []) <|> next

    next :: Parser [(Name,Term,Eras)]
    next = do
      (b, bT) <- binderAndType
      e <- if erasable
           then optional $ (sc >> sym ",") <|> (sc >> sym ";")
           else optional (sc >> sym ",")
      case e of
        Just ";" -> (do bs <- binders [VarB b] $ go; return $ (b,bT,Eras) : bs)
        _        -> (do bs <- binders [VarB b] $ go; return $ (b,bT,Keep) : bs)

    binderAndType :: Parser (Name, Term)
    binderAndType = do
      b <- optional name
      case b of
        Just n -> do
          bT <- sc >> (optional $ sym ":" >> term)
          case bT of
            Just x -> return (n,x)
            Nothing -> (\x -> (n,x)) <$> newHole

        Nothing -> do
          bT <- sym ":" >> term
          return ("_",bT)

-- get a hole with a unique name
newHole :: Parser Term
newHole = do
  h <- gets _holeCount
  modify (\s -> s { _holeCount = (_holeCount s) + 1 })
  return $ Hol $ T.pack ("#" ++ show h)

-- a term grouped by parenthesis
group :: Parser Term
group = do
  sym "("
  ts <- sc >> sepEndBy1 term sc
  lit ")"
  return $ foldl1 (\x y -> App x y Keep) ts

-- an term with lambda-style whitespace applications
group' :: Parser Term
group' = do
  ts <- some term
  return $ foldl1 (\x y -> App x y Keep) ts

-- a self-type
slf :: Parser Term
slf = do
  sym "${"
  n <- name <* sc
  sym "}"
  t <- binders [VarB n] term
  return $ Slf n t

-- a self-type introduction
new :: Parser Term
new = do sym "new("; ty <- term <* sc; sym ")"; ex <- term; return $ New ty ex

-- a self-type elimination
use :: Parser Term
use = do sym "use("; ex <- term <* sc; sym ")"; return $ Use ex;

-- an inline typed log
log :: Parser Term
log = do sym "log("; msge <- term <* sc; sym ")"; Log msge <$> term

-- if-then-else
ite :: Parser Term
ite = do
  c <- sym "if"   >> group' <* sc
  t <- sym "then" >> group' <* sc
  f <- sym "else" >> group' <* sc
  return $ Ite c t f

-- a programmer defined hole
hol :: Parser Term
hol = do n <- sym "?" >> name; return $ Hol n

-- top level term
term :: Parser Term
term = do
  t <- choice
      [ try $ allLam
      , try $ let_
      , try $ typ
      , try $ num
      , try $ slf
      , try $ new
      , try $ log
      , try $ use
      , try $ ite
      , try $ hol
      , try $ val
      , try $ refVar
      , try $ group
      , try $ case_
      --, try $ when_
      --, try $ switch_
      ]
  choice
    [ try $ fun t
    , try $ opr t
    , return t
    ]

-- function style application
fun :: Term -> Parser Term
fun f = do
  as <- concat <$> some args
  return $ foldl (\t (a,e) -> App t a e) f as

-- arguments to a function style application
args :: Parser [(Term, Eras)]
args = sym "(" >> go
  where
    go   = (sc >> lit ")" >> return []) <|> next
    next = do
      a <- term <* sc
      e <- optional $ (sc >> sym ",") <|> (sc >> sym ";")
      case e of
        Just ";"  -> (do as <- go; return $ (a,Eras) : as)
        _         -> (do as <- go; return $ (a,Keep) : as)

-- an operator name
opName :: Parser Text
opName = do
  n  <- satisfy (\x -> elem x opInitSymbol)
  case elem n opSingleSymbol of 
    True -> do
      ns <- many (alphaNumChar <|> satisfy (\x -> elem x opSymbol))
      return $ T.pack (n : ns)
    False -> do
      ns <- some (alphaNumChar <|> satisfy (\x -> elem x opSymbol))
      return $ T.pack (n : ns)
  where
    opInitSymbol :: [Char]
    opInitSymbol = "!$%&*+./<=>/^|~-"
    opSingleSymbol :: [Char]
    opSingleSymbol = "!$%&*+./<>/^|~-"
    opSymbol :: [Char]
    opSymbol = "!#$%&*+./<=>?@/^|~-"

-- binary symbolic operator
opr :: Term -> Parser Term
opr x = do
  sc
  op <- opName <|> sym "::"
  when (op `elem` reservedSymbols) (fail "reservedWord")
  sc
  y <- term
  case op of
    "::"  -> return $ Ann y x
    "->"  -> return $ All "_" x Keep y
    "+"   -> return $ Opr ADD x y
    "-"   -> return $ Opr SUB x y
    "*"   -> return $ Opr MUL x y
    "\\"  -> return $ Opr GTH x y
    "%"   -> return $ Opr MOD x y
    "**"  -> return $ Opr POW x y
    "&&"  -> return $ Opr AND x y
    "||"  -> return $ Opr BOR x y
    "^"   -> return $ Opr XOR x y
    "~"   -> return $ Opr NOT x y
    ">"   -> return $ Opr GTH x y
    "<"   -> return $ Opr LTH x y
    ">>>" -> return $ Opr SHR x y
    "<<"  -> return $ Opr SHL x y
    "===" -> return $ Opr EQL x y
    f     -> return $ App (App (Ref f 0) x Keep) y Keep
  where
    reservedSymbols = ["|", "=>"]

case_ :: Parser Term
case_ = do
  lit "case"
  sc
  match <- term
  sc
  as    <- try $ optional (sym "as" >> name <* sc)
  withs <- try $ many with
  cases <- try $ many c
  type_ <- case cases of
              [] -> Just <$> (sym ":" >> term)
              _  -> optional (sym ":" >> term)
  return $ Cse match withs cases type_

  where
    with :: Parser Term
    with = sym "with" >> term <* sc

    c :: Parser (Name, Term)
    c = do
      sym "|"
      --ls <- gets _names
      n <- name <* sc
      sym "=>"
      t <- term
      sc
      return (n,t)

def :: Parser Def
def = choice
  [ try $ expr
  , try $ enum
  , try $ data_
  , try $ import_
  ]

expr :: Parser Def
expr = do
  (n,t) <- expr' (optional $ sym ";")
  return $ Expr n t

expr' :: Parser a -> Parser (Name, Term)
expr' x = do
  n  <- name
  ls <- asks _block
  ds <- gets _names
  when (Set.member n ls || Set.member n ds) (fail "attempted to redefine a name")
  bs <- (optional $ binds True "(" ")")
  sc
  let ns = maybe [] (fmap (\(a,b,c) -> VarB a)) bs
  t  <- optional (sym ":" >> binders ns term <* sc)
  x
  d  <- binders ns term
  let x = case (bs, t) of
       (Nothing, Nothing) -> d
       (Nothing, Just t)  -> Ann t d
       (Just bs, Nothing) -> foldr (\(n,t,e) x -> Lam n t e x) d bs
       (Just bs, Just t) -> Ann
         (foldr (\(n,t,e) x -> All n t e x) t bs)
         (foldr (\(n,t,e) x -> Lam n t e x) d bs)
  return $ (n,x)

enum :: Parser Def
enum = do
  sym "enum"
  Enum <$> some e 
  where
    e = do
      sym "|"
      ls <- gets _names
      n <- name
      when (Set.member n ls) (fail "attempted to redefine a name")
      sc
      return n

data_ :: Parser Def
data_ = do
  sym "T"
  ls <- gets _names
  n <- name
  when (Set.member n ls) (fail "attempted to redefine a name")
  ps <- optional' $ binds False "{" "}"
  sc
  is <- optional' $ binders ((\(x,y,z) -> VarB x) <$> ps) (binds False "(" ")")
  sc
  cs <- binders ((\(x,y,z) -> VarB x) <$> ps) (many (sym "|" >> ctor))
  return $ Data n (f <$> ps) (f <$> is) cs
  where
  f (a,b,c) = (a,b)

  optional' :: Parser [a] -> Parser [a]
  optional' p = maybe [] id <$> (optional p)

  ctor :: Parser Ctor
  ctor = do
    n  <- name
    ps <- optional' (binds True "(" ")")
    sc
    ix <- optional (sym ":" >> binders ((\(x,y,z) -> VarB x) <$> ps) term <* sc)
    return $ Ctor n (f <$> ps) ix

import_ :: Parser Def
import_ = do
  sym "import"
  n <- name
  h <- maybe "" id <$> optional (sym "#" >> some (satisfy isFileID))
  return $ Impt n (T.pack h)
  where
    isFileID x = elem x (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'])

let_ :: Parser Term
let_ = do
  sym "let"
  ds <- (sym "(" >> lets) <|> (pure <$> (expr' (sym "=") <* sepr))
  t <- binders ((\(a, b) -> RefB a) <$> ds) $ group'
  return $ Let (M.fromList ds) t
  where
    lets :: Parser [(Name, Term)]
    lets = (lit ")" >> sepr >> return []) <|> next

    next :: Parser [(Name, Term)]
    next = do
     ls    <- asks _block
     (n,t) <- expr' (sym "=") <* sepr
     when (Set.member n ls) (fail "attempted to redefine a name")
     ns <- block [n] $ lets
     return $ (n,t) : ns


    sepr :: Parser (Maybe Text)
    sepr = sc >> optional (sym ";" <|> sym ",")

module_ :: Parser [Def]
module_ = sc >> defs
  where
    defs :: Parser [Def]
    defs = (sc >> eof >> return []) <|> next

    next :: Parser [Def]
    next = do
     d  <- def <* sc
     case d of
         Expr n t -> do
           ds <- defs
           return $ d : ds
         Enum ns -> do
           ds <- defs
           return $ d : ds
         Data n _ _ cs -> do
           let cns = (\(Ctor n _ _) -> n) <$> cs
           ds <- defs
           return $ d : ds
         Impt _ _ -> do
           ds <- defs
           return $ d : ds

