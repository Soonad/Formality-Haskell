module Parser.Lang where

import           Prelude                    hiding (log)

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Char
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M

import           Control.Monad.RWS.Lazy     hiding (All)

import           Core                       (Eras (..), Name, Op (..))
import qualified Core                       as Core

import Parser.Types
import Lang

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "//" <|> L.skipLineComment "--") empty

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
dbl :: Parser Term
dbl = lit "Double" >> return Dbl

wrd :: Parser Term
wrd = lit "Word" >> return Wrd

-- numeric U64 value
u64 :: Parser Term
u64 = do
  v <- choice
    [ lit "0x" >> L.hexadecimal
    , lit "0o" >> L.octal
    , lit "0b" >> L.binary
    , L.decimal
    ]
  when ((v :: Integer) >= 2^64) (fail "word too big")
  return $ U64 (fromIntegral v)

bits :: Parser Term
bits = do
  v <- choice
    [ lit "0x" >> L.hexadecimal
    , lit "0o" >> L.octal
    , lit "0b" >> L.binary
    , L.decimal
    ]
  return $ Bit False v

f64 :: Parser Term
f64 = F64 <$> L.signed (pure ()) L.float

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
           then optional $ (sym ",") <|> (sym ";")
           else optional (sym ",")
      case e of
        Just ";" -> (do bs <- binders [VarB b] $ go; return $ (b,bT,Eras) : bs)
        _        -> (do bs <- binders [VarB b] $ go; return $ (b,bT,Keep) : bs)

    binderAndType :: Parser (Name, Term)
    binderAndType = do
      b <- optional name
      case b of
        Just n -> do
          bT <- sc >> (optional $ sym ":" >> term)
          sc
          case bT of
            Just x -> return (n,x)
            Nothing -> (\x -> (n,x)) <$> newHole

        Nothing -> do
          bT <- sym ":" >> term
          sc
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
      , try $ dbl
      , try $ wrd
      , try $ str
      , try $ chr_
      , try $ lst
      , try $ slf
      , try $ new
      , try $ log
      , try $ use
      , try $ ite
      , try $ hol
      , try $ f64
      , try $ u64
      , try $ refVar
      , try $ group
      , try $ cse
      , try $ whn
      , try $ swt
      ]
  t' <- choice
    [ try $ fun t
    , return t
    ]
  choice
    [ try $ opr t'
    , try $ ann t
    , return t'
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
    next = do (a,e) <- holeArg <|> termArg; as <- go; return $ (a,e) : as
    holeArg = sym "_" >> (\x -> (x,Eras)) <$> newHole
    termArg = do
      t <- term
      e <- choice
        [ sym "," >> return Keep
        , sym ";" >> return Eras
        , lookAhead (lit ")") >> return Keep
        ]
      return (t,e)

-- an operator name
opName :: Parser Text
opName = do
  n  <- satisfy (\x -> elem x opInitSymbol)
  case elem n opSingleSymbol of 
    True -> do
      ns <- many (satisfy (\x -> elem x opSymbol))
      return $ T.pack (n : ns)
    False -> do
      ns <- some (satisfy (\x -> elem x opSymbol))
      return $ T.pack (n : ns)
  where
    opInitSymbol :: [Char]
    opInitSymbol = "!$%&*+./\\<=>^|~-"
    opSingleSymbol :: [Char]
    opSingleSymbol = "!$%&*+./\\<>^|~-"
    opSymbol :: [Char]
    opSymbol = "!#$%&*+./\\<=>?@^|~-"

-- binary symbolic operator
opr :: Term -> Parser Term
opr x = do
  sc
  op <- opName
  when (op `elem` reservedSymbols) (fail "reservedWord")
  sc
  y <- term
  case op of
    "->"  -> return $ All "_" x Keep y
    "+"   -> return $ Opr ADD x y
    "-"   -> return $ Opr SUB x y
    "*"   -> return $ Opr MUL x y
    "\\" -> return $ Opr DIV x y
    "/"   -> return $ Opr DIV x y
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

ann :: Term -> Parser Term
ann x = do
  sc
  op <- sym "::"
  y <- rewrite <|> term
  return $ Ann y x
  where
    rewrite :: Parser Term
    rewrite = do
      sym "rewrite"
      p <- term
      sc
      sym "with"
      q <- term
      return $ Rwt p q

cse :: Parser Term
cse = do
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
    with :: Parser (Term,Term)
    with = do
      sym "with" 
      x <- term <* sc
      t <- (sym ":" >> term <* sc) <|> newHole
      return (x,t)


    c :: Parser (Name, Term)
    c = do
      sym "|"
      --ls <- gets _names
      n <- name <* sc
      sym "=>"
      t <- term
      sc
      return (n,t)

whn :: Parser Term
whn = do
  sym "when" 
  ws <- some w
  sc
  sym "else"
  f <- term
  return $ Whn ws f
  where
    w = do sym "|"; c <- term; sc; sym "=>"; t <- term; sc; return (c,t)

swt :: Parser Term
swt = do
  sym "switch"
  n <- term
  sc
  ws <- some w
  sc
  sym "else"
  f <- term
  return $ Swt n ws f
  where
    w = do sym "|"; c <- term; sc; sym "=>"; t <- term; sc; return (c,t)

def :: Parser a -> Parser (Name, Term)
def x = do
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

let_ :: Parser Term
let_ = do
  sym "let"
  ds <- (sym "(" >> lets) <|> (pure <$> (def (sym "=") <* sepr))
  t <- binders ((\(a, b) -> RefB a) <$> ds) $ group'
  return $ Let (M.fromList ds) t
  where
    lets :: Parser [(Name, Term)]
    lets = (lit ")" >> sepr >> return []) <|> next

    next :: Parser [(Name, Term)]
    next = do
     ls    <- asks _block
     (n,t) <- def (sym "=") <* sepr
     when (Set.member n ls) (fail "attempted to redefine a name")
     ns <- block [n] $ lets
     return $ (n,t) : ns

    sepr :: Parser (Maybe Text)
    sepr = sc >> optional (sym ";" <|> sym ",")

str :: Parser Term
str = do
  char '"'
  cs <- many (nonEscape <|> empty <|> (pure <$> escape))
  char '"'
  return $ Str (T.pack (concat cs))
  where
    nonEscape :: Parser [Char]
    nonEscape = pure <$> noneOf ("\\\"" :: String)

    empty :: Parser [Char]
    empty = lit "\\&" >> return []

chr_ :: Parser Term
chr_ = do
  char '\''
  c <- nonEscape <|> escape
  char '\''
  return $ Chr c
  where
    nonEscape :: Parser Char
    nonEscape = noneOf ("\\\'" :: String)

escape :: Parser Char
escape = do
  d <- char '\\'
  choice
    [ lit "\\"  >> return '\\'
    , lit "\""  >> return '"'
    , lit "x"   >> chr <$> L.hexadecimal
    , lit "o"   >> chr <$> L.octal
    , lit "n"   >> return '\n'
    , lit "r"   >> return '\r'
    , lit "v"   >> return '\v'
    , lit "b"   >> return '\b'
    , lit "f"   >> return '\f'
    , lit "ACK" >> return '\ACK'
    , lit "BEL" >> return '\BEL'
    , lit "BS"  >> return '\BS'
    , lit "CR"  >> return '\CR'
    , lit "DEL" >> return '\DEL'
    , lit "DC1" >> return '\DC1'
    , lit "DC2" >> return '\DC2'
    , lit "DC3" >> return '\DC3'
    , lit "DC4" >> return '\DC4'
    , lit "DLE" >> return '\DLE'
    , lit "ENQ" >> return '\ENQ'
    , lit "EOT" >> return '\EOT'
    , lit "ESC" >> return '\ESC'
    , lit "ETX" >> return '\ETX'
    , lit "ETB" >> return '\ETB'
    , lit "EM"  >> return '\EM'
    , lit "FS"  >> return '\FS'
    , lit "FF"  >> return '\FF'
    , lit "GS"  >> return '\GS'
    , lit "HT"  >> return '\HT'
    , lit "LF"  >> return '\LF'
    , lit "NUL" >> return '\NUL'
    , lit "NAK" >> return '\NAK'
    , lit "RS"  >> return '\RS'
    , lit "SOH" >> return '\SOH'
    , lit "STX" >> return '\STX'
    , lit "SUB" >> return '\SUB'
    , lit "SYN" >> return '\SYN'
    , lit "SI"  >> return '\SI'
    , lit "SO"  >> return '\SO'
    , lit "SP"  >> return '\SP'
    , lit "US"  >> return '\US'
    , lit "VT"  >> return '\VT'
    , lit "^@"  >> return '\0'
    , lit "^["  >> return '\ESC'
    , lit "^\\" >> return '\FS'
    , lit "^]"  >> return '\GS'
    , lit "^^"  >> return '\RS'
    , lit "^_"  >> return '\US'
    , do lit "^"; c <- oneOf ['A'..'Z']; return (chr $ (ord c) - 64)
    , chr <$> L.decimal
    ]

lst :: Parser Term
lst = Lst <$> (sym "[" >> go)
  where
    go   = (sc >> lit "]" >> return []) <|> next
    next = do 
      a <- term <* sc
      sym "," <|> lookAhead (lit "]")
      as <- go
      return $ a : as

