module Lang where

import           Prelude                    hiding (log)

import           Data.Char
import           Data.List                  hiding (group)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (isJust,fromJust)
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Control.Monad              (void)
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy    hiding (All)

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Debug

import           Check hiding (newHole, _context, binder, Binder)
import           Core
import           Pretty

-- binders can bind variables (deBruijn) or references
data Binder = VarB Name | RefB Name deriving (Eq, Show)

-- track Holes (meta-variables) for unique names
data ParseState = ParseState { _holeCount :: Int } deriving Show

-- track binding contexts from lets, lambdas or foralls
data ParseEnv = ParseEnv { _context :: [Binder] } deriving Show

-- add a list of binders to the context
binders :: [Binder] -> Parser a -> Parser a
binders bs p = local (\e -> e { _context = (reverse bs) ++ _context e }) p

-- a parser is a Reader-Writer-State monad transformer wrapped over
-- a ParsecT over Text
-- TODO : Custom error messages
type Parser = RWST ParseEnv () ParseState (ParsecT Void Text Identity)

-- top level parser with default env and state
parseDefault :: Show a => Parser a -> Text
             -> Identity
                  (Either (ParseErrorBundle Text Void)
                          (a, ParseState, ())
                  )
parseDefault p s = runParserT (runRWST p (ParseEnv []) (ParseState 0)) "" s

-- a useful testing function
parserTest :: Show a => Parser a -> Text -> IO ()
parserTest p s = print $
  runParserT (runRWST p (ParseEnv []) (ParseState 0)) "" s

-- evals the term directly
evalTest :: Parser Term -> Text -> IO ()
evalTest p s = do
  let Identity (Right (a,st,w)) =
        runParserT (runRWST p (ParseEnv []) (ParseState 0)) "" s
  print $ a
  print $ eval a M.empty

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
    nameSymbol = "_.#-@/'"
    reservedWords :: [Text]
    reservedWords = ["let", "rewrite"]

-- resolves if a name is a variable or reference
refVar :: Parser Term
refVar = do
  ctx <- asks _context
  is <- optional (some (lit "^"))
  n <- name
  let carets = (maybe 0 id (length <$> is))
  return $ go ctx carets 0 0 n
  where
    go (x:xs) cs varIndex refCount n
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
  bs <- binds
  sc
  ctor <- (sym "->" >> return All) <|> (sym "=>" >> return Lam)
  sc
  body <- binders ((\(x,y,z) -> VarB x) <$> bs) expr
  return $ foldr (\(n,t,e) x -> ctor n t e x) body bs

-- binders in a forall or lambda
binds :: Parser [(Name, Term, Eras)]
binds = sym "(" >> go
  where
    go = (sc >> lit ")" >> return []) <|> next

    next :: Parser [(Name,Term,Eras)]
    next = do
      (b, bT) <- binderAndType
      e <- optional $ (sc >> sym ",") <|> (sc >> sym ";")
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
  c <- sym "if"   >> term <* sc
  t <- sym "then" >> term <* sc
  f <- sym "else" >> term <* sc
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
  sc
  y <- term
  case op of
    "::" -> return $ Ann y x
    "->" -> return $ All "_" x Keep y
    "+"  -> return $ Op2 ADD x y
    "-"  -> return $ Op2 SUB x y
    "*"  -> return $ Op2 MUL x y
    "==" -> return $ Op2 EQL x y
    f    -> return $ App (App (Ref f 0) x Keep) y Keep

-- an expression with lambda-style applications
expr :: Parser Term
expr = do
  ts <- some term
  return $ foldl1 (\x y -> App x y Keep) ts

-- a definition
def :: Parser (Name, Term)
def = do 
  n  <- name
  bs <- (optional $ binds)
  sc
  let ns = maybe [] (fmap (\(a,b,c) -> VarB a)) bs
  t  <- optional (sym ":" >> binders ns term <* sc)
  optional (sym "=")
  d  <- binders ns expr
  case (bs, t) of
    (Nothing, Nothing) -> return (n, d)
    (Nothing, Just t)  -> return $ (n, Ann t d)
    (Just bs, Nothing) -> return $ (n, foldr (\(n,t,e) x -> Lam n t e x) d bs)
    (Just bs, Just t) -> 
      let typ = foldr (\(n,t,e) x -> All n t e x) t bs
          trm = foldr (\(n,t,e) x -> Lam n t e x)  d bs
       in return $ (n, Ann typ trm)

let_ :: Parser Term
let_ = do
  sym "let"
  r <- optional (sym "type")
  let r' = if isJust r then Equi else Norm
  (n, t) <- def
  sc
  optional (sym ";")
  b <- binders [RefB n] $ expr
  return $ Let n t r' b

file :: Parser (M.Map Name [(Recr,Term)])
file = do; sc; ds <- (sepEndBy1 def' sc); eof; return $ M.fromList ds
  where
    def' :: Parser (Name, [(Recr,Term)])
    def' = do
      r <- optional (sym "type")
      let r' = if isJust r then Equi else Norm
      (n,d) <- def
      return $ (n,[(r', d)])

