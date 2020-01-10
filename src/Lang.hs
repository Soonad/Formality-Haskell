module Lang where

import           Prelude                    hiding (log)

import           Data.Char
import           Data.List                  hiding (group)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (isJust)
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Void

import           Control.Monad              (void)
import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Debug

import           Check hiding (newHole)
import           Core
import           Pretty

type Scope = M.Map Name Term

data Ctx = Ctx { binders :: [Text], holeCount :: Int } deriving Show

type Parser = StateT Ctx (ParsecT Void Text Identity)

parserTest :: Show a => Parser a -> Text -> IO ()
parserTest p s = print $ runParserT (runStateT p (Ctx [] 0)) "" s

-- for `dbg`
--type Parser = ParsecT Void Text (State Ctx)
--
--parserTest :: Show a => Parser a -> Text -> IO ()
--parserTest p s = print $ runState (runParserT p "" s) (Ctx [] 0)

-- space consumer
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "//") empty

sym = L.symbol sc
lit = string

evalTest :: Parser Term -> Text -> IO ()
evalTest p s = do
  let Identity (Right (a, b)) = runParserT (runStateT p (Ctx [] 0)) "" s
  print $ eval a M.empty

name :: Parser Text
name = do
  us <- many (lit "_")
  n  <- if us == [] then letterChar else alphaNumChar
  ns <- many (alphaNumChar <|> satisfy (\x -> elem x nameSymbol))
  return $ T.concat [T.concat us, T.pack (n : ns)]
  where
    nameSymbol :: [Char]
    nameSymbol = "_.#-@/'"

refVar :: Parser Term
refVar = do
  bs <- gets binders
  n <- name
  case findIndex (\x -> x == n) bs of
    Just i -> return $ Var i
    _      -> return $ Ref n

num :: Parser Term
num = lit "Number" >> return Num

val :: Parser Term
val = Val <$> L.decimal

typ :: Parser Term
typ = lit "Type" >> return Typ

allLam :: Parser Term
allLam = do
  bs <- binds
  sc
  ctor <- (sym "->" >> return All) <|> (sym "=>" >> return Lam)
  sc
  body <- expr
  return $ foldr (\(n,t,e) x -> ctor n t e x) body bs

binds :: Parser [(Name, Term, Eras)]
binds = sym "(" >> go
  where
    go = (sc >> lit ")" >> return []) <|> next

    next :: Parser [(Name,Term,Eras)]
    next = do
      (b, bT) <- binderAndType
      e <- optional $ (sc >> sym ",") <|> (sc >> sym ";")
      case e of
        Just ";" -> (do bs <- go; return $ (b,bT,Eras) : bs)
        _        -> (do bs <- go; return $ (b,bT,Keep) : bs)

    binderAndType :: Parser (Name, Term)
    binderAndType = do
      b <- optional name
      case b of
        Just n -> do
          bT <- sc >> (optional $ sym ":" >> term)
          modify (\ctx -> ctx { binders = n : binders ctx })
          case bT of
            Just x -> return (n,x)
            Nothing -> (\x -> (n,x)) <$> newHole

        Nothing -> do
          bT <- sym ":" >> term
          return ("_",bT)

newHole :: Parser Term
newHole = do
  h <- gets holeCount
  modify (\ctx -> ctx { holeCount = (holeCount ctx) + 1 })
  return $ Hol $ T.pack ("#" ++ show h)

group :: Parser Term
group = do
  sym "("
  ts <- sc >> sepEndBy1 term sc
  lit ")"
  return $ foldl1 (\x y -> App x y Keep) ts

slf :: Parser Term
slf = do
  sym "${"
  n <- name <* sc
  modify (\ctx -> ctx { binders = n : binders ctx })
  sym "}"
  t <- term
  return $ Slf n t

new :: Parser Term
new = do sym "new("; ty <- term <* sc; sym ")"; ex <- term; return $ New ty ex

use :: Parser Term
use = do sym "use("; ex <- term <* sc; sym ")"; return $ Use ex;

log :: Parser Term
log = do sym "log("; msge <- term <* sc; sym ")"; Log msge <$> term

ite :: Parser Term
ite = do
  c <- sym "if"   >> term <* sc
  t <- sym "then" >> term <* sc
  f <- sym "else" >> term <* sc
  return $ Ite c t f

hol :: Parser Term
hol = do n <- sym "?" >> name; return $ Hol n

term :: Parser Term
term = do
  t <- choice
      [ try $ allLam
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

fun :: Term -> Parser Term
fun f = do
  as <- concat <$> some args
  return $ foldl (\t (a,e) -> App t a e) f as

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

opName :: Parser Text
opName = do
  n  <- satisfy (\x -> elem x opInitSymbol) 
  ns <- many (alphaNumChar <|> satisfy (\x -> elem x opSymbol))
  return $ T.pack (n : ns)
  where
    opInitSymbol :: [Char]
    opInitSymbol = "!$%&*+./<=>/^|~-"
    opSymbol :: [Char]
    opSymbol = "!#$%&*+./<=>?@/^|~"

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
    f    -> return $ App (App (Ref f) x Keep) y Keep

expr :: Parser Term
expr = do
  ts <- some term
  return $ foldl1 (\x y -> App x y Keep) ts

def :: Parser (Name, Term)
def = do
  n  <- name <* sc
  bs <- (optional $ binds <* sc)
  t  <- optional (sym ":" >> term <* sc)
  d  <- expr
  case (bs, t) of
    (Nothing, Nothing) -> return (n, d)
    (Nothing, Just t)  -> return $ (n, Ann t d)
    (Just bs, Nothing) -> return $ (n, foldr (\(n,t,e) x -> Lam n t e x) d bs)
    (Just bs, Just t) -> 
      let typ = foldr (\(n,t,e) x -> All n t e x) t bs
          trm = foldr (\(n,t,e) x -> Lam n t e x)  d bs
       in return $ (n, Ann typ trm)

file :: Parser (M.Map Name Term)
file = do
  sc
  ds <- (sepEndBy1 def sc)
  eof
  return $ M.fromList ds

