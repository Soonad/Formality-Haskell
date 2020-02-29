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
  ns <- many (alphaNumChar <|> oneOf nameSymbol)
  let nam = T.concat [T.concat us, T.pack (n : ns)]
  if nam `elem` reservedWords then fail "reservedWord" else return nam
  where
    nameSymbol = "_.-@/'" :: [Char]
    reservedWords = ["let", "T", "case", "with"] :: [Text]

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

f64 :: Parser Term
f64 = F64 <$> L.signed (pure ()) L.float

bit :: Parser Term
bit = do
  v <- choice
    [ lit "0x" >> L.hexadecimal
    , lit "0o" >> L.octal
    , lit "0d" >> L.decimal
    , L.binary
    ]
  t <- (lit "b" >> return False) <|> (lit "B" >> return True)
  return $ Bit t v

nat :: Parser Term
nat = do
  v <- choice
    [ lit "0x" >> L.hexadecimal
    , lit "0o" >> L.octal
    , lit "0b" >> L.binary
    , L.decimal
    ]
  t <- (lit "n" >> return False) <|> (lit "N" >> return True)
  return $ Nat t v


-- The type "Type"
typ :: Parser Term
typ = lit "Type" >> return Typ

-- forall or lambda
allLam :: Parser Term
allLam = do
  bs <- binds True "(" ")"
  sc
  ctor <- (sym "->" >> return All) <|> (sym "=>" >> return Lam)
  body <- binders ((\(x,y,z) -> VarB x) <$> bs) term
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
      b <- optional $ (try $ lit "_") <|> name
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

-- a self-type
slf :: Parser Term
slf = do
  n <- (sym "${" >> name <* sc <* sym "}")
  Slf n <$> binders [VarB n] term

-- a self-type introduction
new :: Parser Term
new = New <$> (sym "new(" >> term <* sc <* sym ")") <*> term

-- a self-type elimination
use :: Parser Term
use = Use <$> (sym "use(" >> term <* sc <* sym ")")

-- an inline typed log
log :: Parser Term
log = Log <$> (sym "log(" >> term <* sc <* sym ")") <*> term

-- if-then-else
ite :: Parser Term
ite = Ite <$> (sym "if" >> term <* sc)
          <*> (sym "then" >> term <* sc)
          <*> (sym "else" >> term <* sc)

-- a programmer defined hole
hol :: Parser Term
hol = sym "?" >> (Hol <$> name <|> newHole)

term :: Parser Term
term = do
  t <- term' <|> group
  t' <- try $ fun t <|> return t
  choice
    [ try $ ann t'
    , try $ opr t'
    , return t'
    ]
  where
    group :: Parser Term
    group = sym "(" >> foldApp <$> (sc >> sepEndBy1 term sc) <* lit ")"
    foldApp = foldl1 (\x y -> App x y Keep)

    term' :: Parser Term
    term' = choice
      [ try $ allLam
      , try $ let_
      , try $ get_
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
      , try $ bit
      , try $ nat
      , try $ f64
      , try $ u64
      , try $ refVar
      , try $ cse
      , try $ mth
      , try $ whn
      , try $ swt
      , try $ lst
      , try $ par
      , try $ pTy
      ]

-- function style application
fun :: Term -> Parser Term
fun f = foldl (\t (a,e) -> App t a e) f <$> (concat <$> some args)

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
        , lookAhead (try $ sc >> lit ")") >> return Keep
        ]
      return (t,e)

-- an operator name
opName :: Parser Text
opName = do
  n  <- oneOf opInitSymbol
  case elem n opSingleSymbol of
    True  -> T.pack . (n:) <$> many (oneOf opSymbol)
    False -> T.pack . (n:) <$> some (oneOf opSymbol)
  where
    opInitSymbol   = "!$%&*+./\\<=>^|~-"    :: [Char]
    opSingleSymbol = "!$%&*+./\\<>^|~-"     :: [Char]
    opSymbol       = "!#$%&*+./\\<=>?@^|~-" :: [Char]

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
    "\\"  -> return $ Opr DIV x y
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
ann x = (\y -> Ann y x) <$> (sc >> sym "::" >> (rwt <|> term))
  where
    rwt = Rwt <$> (sym "rewrite" >> term <* sc) <*> (sym "with" >> term)

-- case expression
--
-- case x as y
-- with c : P
-- | foo => 1
-- | bar => 2
-- : Q
cse :: Parser Term
cse = do
  sym "case"
  match <- term <* sc
  as    <- optional (sym "as" >> name <* sc)
  withs <- sepBy' wit sc
  case withs of
    [] -> do
      cases <- sepBy' cas sc
      case cases of
        [] -> Cse match [] [] <$> Just <$> (sym ":" >> term)
        _  -> Cse match [] cases <$> (optional $ try $ (sc >> sym ":" >> term))
    _  -> Cse match withs
            <$> (sc >> sepBy1' cas sc)
            <*> (optional $ try $ (sc >> sym ":" >> term))
  where
    cas :: Parser (Name, Term)
    cas = (,) <$> (sym "|" >> name <* sc) <*> (sym "=>" >> term)

    wit :: Parser (Term,Term)
    wit = (,) <$> (sym "with" >> term <* sc)
              <*> ((sym ":" >> term <* sc) <|> newHole)

-- rust-style match expression
-- match x as y
-- with c : P
-- { foo => 1,
--   bar => 2
-- } : Word

mth :: Parser Term
mth = do
  sym "match"
  x  <- term <* sc
  as <- (optional (sym "as" >> name <* sc))
  ws <- sepBy' wit sc
  sym "{"
  cs <- sepBy' ((,) <$> (name <* sc) <*> (sym "=>" >> term)) (sc >> sym ",")
  sc >> sym "}"
  t <- optional $ try $ (sc >> sym ":" >> term)
  return $ Cse x ws cs t
  where
    wit :: Parser (Term,Term)
    wit = (,) <$> (sym "with" >> term <* sc)
              <*> ((sym ":" >> term <* sc) <|> newHole)

-- Megaparsec sepBy is eager, we need non-eager sep
sepBy1' p sep = (:) <$> p <*> many (try $ sep >> p)
sepBy'  p sep = sepBy1' p sep <|> pure []
-- Parses at least 2
sepBy2' p sep = (:) <$> (p <* sep) <*> sepBy1' p sep


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
  sc
  t <- binders ((\(a, b) -> RefB a) <$> ds) $ term
  return $ Let (M.fromList ds) t
  where
    sepr :: Parser (Maybe Text)
    sepr = optional $ try $ (sc >> lit ";")

    lets :: Parser [(Name, Term)]
    lets = (lit ")" >> sepr >> return []) <|> next

    next :: Parser [(Name, Term)]
    next = do
     ls    <- asks _block
     (n,t) <- def (sym "=") <* (sepr >> sc)
     when (Set.member n ls) (fail "attempted to redefine a name")
     ns <- block [n] $ lets
     return $ (n,t) : ns

get_ :: Parser Term
get_ = do
  sym "get" >> (sym "[" <|> sym "#[")
  x <- name <* sc <* sym ","
  y <- name <* sc <* sym "]"
  sym "="
  t <- term <* sc <* optional (sym ";")
  b <- binders [RefB x, RefB y] term
  return $ Get x y t b

str :: Parser Term
str = do
  char '"'
  cs <- many $ nonEscape <|> empty <|> (pure <$> esc)
  char '"'
  return $ Str . T.pack . concat $ cs
  where
    nonEscape :: Parser [Char]
    nonEscape = pure <$> noneOf ("\\\"" :: String)

    empty :: Parser [Char]
    empty = lit "\\&" >> return []

chr_ :: Parser Term
chr_ = Chr <$> (char '\'' >> (noneOf ("\\\'" :: String) <|> esc) <* char '\'')

esc :: Parser Char
esc = do
  char '\\'
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
    , (\ c -> chr $ (ord c) - 64) <$> (lit "^" >> oneOf ['A'..'Z'])
    , chr <$> L.decimal
    ]

lst :: Parser Term
lst = Lst <$> choice
  [ sym "[" >> sepBy' term (sc >> sym ",") <* (sc >> lit "]")
  , sym "{" >> sepBy' keyVal (sc >> sym ",") <* (sc >> lit "}")
  ]
  where
  keyVal = do p <- term; sc; sym ":"; q <- term; return $ Par [p,q]

-- pair value
par :: Parser Term
par = Par <$> choice 
  [ sym "(" >> sepBy2' term (sc >> sym ",") <* (sc >> lit ")")
  , sym "#[" >> sepBy2' term (sc >> sym ",") <* (sc >> lit "]")
  ]

-- pair type
pTy :: Parser Term
pTy = PTy <$> choice
  [ sym "#(" >> sepBy2' term (sc >> sym ",") <* (sc >> lit ")")
  , sym "#{" >> sepBy2' term (sc >> sym ",") <* (sc >> lit "}")
  ]

-- Sigma type
sig :: Parser Term
sig = do
  sym "["
  ns <- sepBy' p (sc >> sym ",")
  x  <- sym "," >> term
  sym "]"
  return $ Sig ns x
  where
    p = (,) <$> (optional $ name <* sc) <*> term

