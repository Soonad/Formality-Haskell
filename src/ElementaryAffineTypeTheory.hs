-- This file is an complete port of our type-theory to Haskell. It consists of
-- elementary affine logic (EAL) with dependent types, self-types and mutual
-- recursion on the type level. In this small theory, we're able to prove
-- induction for λ-encoded datatypes, giving us inductive datatypes, like
-- Agda's and Coq's.
--
-- We conjecture this language is consistent, since 1. EAL is terminating,
-- which should extend to the dependently-typed case, 2. allowing for mutual
-- recursion at the type level shouldn't change this fact, since, for example,
-- even the untyped core of this language is terminating, i.e., this fact
-- doesn't depend on types, allowing us to have more powerful type-level
-- features. See this Stack Exchange question for a reference:
-- https://bit.ly/2KEz9a1
--
-- The language we're developing, Formality, is a small extension of this
-- theory, adding pairs, ints and other minor features to it, plus a bunch of
-- syntax-sugars to make programming easier. The questions that must be
-- answered, thus, are:
--
-- 1. If the type-theory implemented here is consistent, how can we prove it?
--
-- 2. If not, then how do could we correctly add dependent & inductive types to EAL?
--
-- 3. Is it ok to use affine variables multiple times in types?
--
-- 4. Is it ok to disable EAL's stratification checks in types?
--
-- 5. Are the type-checking rules here correct (for example, for dups)?
--
-- 6. When checking for equality, can we erase duplications and boxes?
--
-- 7. Can we have `Type : Type` (for the same reason we have type recursion)?
--
-- 8. Can we have Cedille-like heterogeneous equality and casts?
--
-- In short, we're looking for the best and simplest way to extend EAL with
-- dependent types and inductive datatypes, and this is our current solution.
-- We're heavily inspired by Cedille and Aaron Stump's work, but, instead of
-- dependent intersections for induction, we use his older, but considerably
-- simpler, self-types approach, taking advantage of the conjecture that we can
-- have mutual recursion. If, for some reason, this doesn't work, then we can
-- fallback to dependent intersections.
--
-- Notes:
--
-- 1. I'll add a lot comments explaining each part of this file soon, in order
--    to explain precisely everything we did here and make this as clear as
--    possible.
--
-- 2. This file wasn't very tested and could have mistakes.
--
-- 3. The stratification checks are missing and will be added soon.

import Data.Char
import Data.List
import Data.Maybe
import Debug.Trace
import qualified Data.Map.Strict as M

type Name
  = String

data Term
  = Var Int
  | Typ
  | All Name Term Term
  | Lam Name Term Term
  | App Term Term
  | Box Term
  | Put Term
  | Dup Name Term Term
  | Slf Name Term
  | New Term Term
  | Use Term
  | Ref Name
  | Ann Term Term
  deriving Show

type Defs 
  = M.Map String (Term, Term)

-- :::::::::::::
-- :: Parsing ::
-- :::::::::::::

skipSpace :: String -> String
skipSpace (' '  : code) = skipSpace code
skipSpace ('\n' : code) = skipSpace code
skipSpace code          = code

parseName :: String -> (String, String) 
parseName = go where
  go (c : code0)
    | isAlphaNum c = let (code1, name) = parseName code0 in (code1, c : name)
    | otherwise    = (c : code0, "")
  go [] = ("", "")

parseChar :: String -> (String, Char)
parseChar = go . skipSpace where
  go (c : code) = (code, c)
  go []         = error "bad-parse"

parseThis :: String -> Char -> (String, Char)
parseThis code c = go (skipSpace code) c where
  go (c : code) e = if c == e then (code, c) else error ("bad-parse: expected " ++ show e ++ ", found " ++ show c)
  go []         e = error ("bad-parse: expected " ++ show e ++ ", found <end>")

parseTerm :: String -> [String] -> (String, Term)
parseTerm code ctx = go (skipSpace code) ctx where
  go ('*' : code0) ctx =
    (code0, Typ)
  go ('{' : code0) ctx =
    let (code1, name) = parseName code0
        (code2, _   ) = parseThis code1 ':'
        (code3, bind) = parseTerm code2 ctx
        (code4, _   ) = parseThis code3 '}'
        (code5, arrw) = parseChar code4
        (code6, _   ) = parseThis code5 '>'
        (code7, body) = parseTerm code6 (name : ctx)
    in (code7, (if arrw == '-' then All else Lam) name bind body)
  go ('(' : code0) ctx =
    let (code1, func) = parseTerm code0 ctx
        (code2, argm) = parseTerm code1 ctx
        (code3, _   ) = parseThis code2 ')'
    in (code3, App func argm)
  go ('!' : code0) ctx =
    let (code1, expr) = parseTerm code0 ctx
    in (code1, Box expr)
  go ('#' : code0) ctx =
    let (code1, expr) = parseTerm code0 ctx
    in (code1, Put expr)
  go ('@' : code0) ctx =
    let (code1, name) = parseName code0
        (code2, _   ) = parseThis code1 '='
        (code3, expr) = parseTerm code2 ctx
        (code4, _   ) = parseThis code3 ';'
        (code5, body) = parseTerm code4 (name : ctx)
    in (code5, Dup name expr body)
  go ('$' : code0) ctx =
    let (code1, name) = parseName code0
        (code2, styp) = parseTerm code1 (name : ctx)
    in (code2, Slf name styp)
  go ('&' : code0) ctx =
    let (code1, styp) = parseTerm code0 ctx
        (code2, expr) = parseTerm code1 ctx
    in (code2, New styp expr)
  go ('%' : code0) ctx =
    let (code1, expr) = parseTerm code0 ctx
    in (code1, Use expr)
  go code0 ctx =
    let (code1, name) = parseName code0
    in (code1, case findIndex (== name) ctx of
         Just i  -> Var i
         Nothing -> Ref name)

parse :: String -> M.Map String (Term, Term)
parse [] = M.empty
parse code0 =
  let (code1, name) = parseName code0
      (code2, _   ) = parseThis code1 ':'
      (code3, ttyp) = parseTerm code2 []
      (code4, _   ) = parseThis code3 '='
      (code5, tval) = parseTerm code4 []
      (code6, _   ) = parseThis code5 ';'
  in M.insert name (ttyp, tval) (parse code6)

-- ::::::::::::::::
-- :: Formatting ::
-- ::::::::::::::::

format :: Term -> [String] -> String
format (Var i)              ctx = if i < length ctx then ctx !! i else "^" ++ show i
format Typ                  ctx = "*"
format (All name bind body) ctx = "{" ++ name ++ " : " ++ format bind ctx ++ "} -> " ++ format body (name : ctx)
format (Lam name bind body) ctx = "{" ++ name ++ " : " ++ format bind ctx ++ "} => " ++ format body (name : ctx)
format (App func argm)      ctx = "(" ++ format func ctx ++ " " ++ format argm ctx ++ ")"
format (Box expr)           ctx = "!" ++ format expr ctx
format (Put expr)           ctx = "#" ++ format expr ctx
format (Dup name expr body) ctx = "@" ++ name ++ " = " ++ format expr ctx ++ "; " ++ format body (name : ctx)
format (Slf name styp)      ctx = "$" ++ name ++ " " ++ format styp (name : ctx)
format (New styp expr)      ctx = "&" ++ format styp ctx ++ " " ++ format expr ctx
format (Use expr)           ctx = "%" ++ format expr ctx
format (Ref name)           ctx = name
format (Ann ttyp tval)      ctx = format tval ctx

-- ::::::::::::::::::
-- :: Substitution ::
-- ::::::::::::::::::

shift :: Term -> Int -> Int -> Term
shift (Var indx)           inc dep = Var (if indx < dep then indx else indx + inc)
shift Typ                  inc dep = Typ
shift (All name bind body) inc dep = All name (shift bind inc dep) (shift body inc (dep + 1))
shift (Lam name bind body) inc dep = Lam name (shift bind inc dep) (shift body inc (dep + 1))
shift (App func argm)      inc dep = App (shift func inc dep) (shift argm inc dep)
shift (Box expr)           inc dep = Box (shift expr inc dep)
shift (Put expr)           inc dep = Put (shift expr inc dep)
shift (Dup name expr body) inc dep = Dup name (shift expr inc dep) (shift body inc (dep + 1))
shift (Slf name styp)      inc dep = Slf name (shift styp inc (dep + 1))
shift (New styp expr)      inc dep = New (shift styp inc dep) (shift expr inc dep)
shift (Use expr)           inc dep = Use (shift expr inc dep)
shift (Ref name)           inc dep = Ref name
shift (Ann ttyp tval)      inc dep = Ann (shift ttyp inc dep) (shift tval inc dep)

subst :: Term -> Term -> Int -> Term
subst (Var indx)           val dep = if dep == indx then val else Var (indx - (if indx > dep then 1 else 0))
subst Typ                  val dep = Typ
subst (All name bind body) val dep = All name (subst bind val dep) (subst body (shift val 1 0) (dep + 1))
subst (Lam name bind body) val dep = Lam name (subst bind val dep) (subst body (shift val 1 0) (dep + 1))
subst (App func argm)      val dep = App (subst func val dep) (subst argm val dep)
subst (Box expr)           val dep = Box (subst expr val dep)
subst (Put expr)           val dep = Put (subst expr val dep)
subst (Dup name expr body) val dep = Dup name (subst expr val dep) (subst body (shift val 1 0) (dep + 1))
subst (Slf name styp)      val dep = Slf name (subst styp (shift val 1 0) (dep + 1))
subst (New styp expr)      val dep = New (subst styp val dep) (subst expr val dep)
subst (Use expr)           val dep = Use (subst expr val dep)
subst (Ref name)           val dep = Ref name
subst (Ann ttyp tval)      val dep = Ann (subst ttyp val dep) (subst tval val dep)

-- ::::::::::::::::
-- :: Evaluation ::
-- ::::::::::::::::

eval :: Term -> Defs -> Term
eval (Var indx)           defs = Var indx 
eval Typ                  defs = Typ
eval (All name bind body) defs = All name bind body
eval (Lam name bind body) defs = Lam name bind (eval body defs)
eval (App func argm)      defs = case eval func defs of
  (Lam name' bind' body')      -> eval (subst body' argm 0) defs
  (Dup name' expr' body')      -> Dup name' expr' (App body' (shift argm 1 0))
  func                         -> App func (eval argm defs)
eval (Dup name expr body) defs = case eval expr defs of
  (Put expr')                  -> eval (subst body expr' 0) defs 
  (Dup name' expr' body')      -> Dup name' expr' (Dup name body' (shift body 1 1))
  expr                         -> Dup name expr body
eval (Slf name styp)      defs = Slf name styp
eval (New styp expr)      defs = eval expr defs
eval (Use expr)           defs = eval expr defs
eval (Ref name)           defs = maybe (Ref name) (\x -> eval (snd x) defs) (M.lookup name defs)
eval (Ann ttyp tval)      defs = eval tval defs

-- ::::::::::::::
-- :: Equality ::
-- ::::::::::::::

data IsEq
  = Eql Term Term
  | And IsEq IsEq
  | Or  IsEq IsEq
  | Ret Bool
  deriving Show

equal :: Term -> Term -> Defs -> Bool
equal a b defs = go (Eql a b) where
  go :: IsEq -> Bool
  go (Ret v) = v
  go iseq    = go (step iseq)
  step :: IsEq -> IsEq
  step (Eql a b) = let
    a0 = eval a M.empty
    b0 = eval b M.empty
    a1 = eval a defs
    b1 = eval b defs
    ex = case (a0, b0) of
      (Ref aName, Ref bName) -> if aName == bName then Just (Ret True) else Nothing
      (App aFunc aArgm, App bFunc bArgm) -> Just (And (Eql aFunc bFunc) (Eql aArgm bArgm))
      otherwise -> Nothing
    ey = case (a1, b1) of
      (Var aIndx             , Var bIndx)             -> Ret (aIndx == bIndx) 
      (Typ                   , Typ)                   -> Ret True
      (All aName aBind aBody , All bName bBind bBody) -> And (Eql aBind bBind) (Eql aBody bBody)
      (Lam aName aBind aBody , Lam bName bBind bBody) -> Eql aBody bBody
      (App aFunc aArgm       , App bFunc bArgm)       -> And (Eql aFunc bFunc) (Eql aArgm bArgm)
      (Box aExpr             , Box bExpr)             -> Eql aExpr bExpr
      (Put aExpr             , Put bExpr)             -> Eql aExpr bExpr
      (Dup aName aExpr aBody , Dup bName bExpr bBody) -> And (Eql aExpr bExpr) (Eql aBody bBody)
      (Slf aName aStyp       , Slf bName bStyp)       -> Eql aStyp bStyp
      (New aStyp aExpr       , New bStyp bExpr)       -> Eql aExpr bExpr
      (Use aExpr             , Use bExpr)             -> Eql aExpr bExpr
      (Ann aTtyp aTval       , Ann bTtyp bTval)       -> Eql aTval bTval
      otherwise                                       -> Ret False
    in case ex of
      Just ex -> Or ex ey
      Nothing -> ey 
  step (And (Ret False) y) = Ret False
  step (And (Ret True) y)  = y
  step (And x (Ret False)) = Ret False
  step (And x (Ret True))  = x
  step (And x y)           = And (step x) (step y)
  step (Or (Ret True) y)   = Ret True
  step (Or (Ret False) y)  = y
  step (Or x (Ret True))   = Ret True
  step (Or x (Ret False))  = x
  step (Or x y)            = Or (step x) (step y)
  step (Ret v)             = Ret v

-- :::::::::::::::::::
-- :: Type-Checking ::
-- :::::::::::::::::::

type Ctx = [(Name, Term)]

match :: Term -> Term -> Defs -> Ctx -> Either String ()
match a b defs ctx | equal a b defs = Right ()
                   | otherwise      = Left ("Type mismatch.\n- Found type... " ++ format a (map fst ctx) ++ "\n- Instead of... " ++ format b (map fst ctx))

check :: Term -> Defs -> Ctx -> Either String Term
check (Var indx) defs ctx = do
  return (shift (snd (ctx !! indx)) (indx + 1) 0)
check Typ defs ctx = do
  return Typ
check (All name bind body) defs ctx = do
  bind_t <- check bind defs ctx
  body_t <- check body defs ((name, bind) : ctx)
  match bind_t Typ defs ctx
  match body_t Typ defs ctx
  return Typ
check (Lam name bind body) defs ctx = do
  body_t <- check body defs ((name, bind) : ctx)
  let term_t = All name bind body_t
  check term_t defs ctx
  return term_t
check (App func argm) defs ctx = do
  func_t <- check func defs ctx
  case eval func_t defs of
    All fName fBind fBody -> do
      argm_t <- check argm defs ctx  
      match argm_t fBind defs ctx
      return (subst fBody (Ann fBind argm) 0)
    otherwise -> Left $ "Non-function application: " ++ format (eval (App func argm) defs) []
check (Box expr) defs ctx = do
  expr_t <- check expr defs ctx
  match expr_t Typ defs ctx
  return Typ
check (Put expr) defs ctx = do
  term_t <- check expr defs ctx
  return (Box term_t)
check (Dup name expr body) defs ctx = do
  expr_t <- check expr defs ctx
  case eval expr_t defs of
    Box tExpr -> do
      let term_v = Ann tExpr (Dup name expr (Var 0))
      check (subst body term_v 0) defs ctx
    otherwise ->
      Left "Unboxed duplication."
check (Slf name styp) defs ctx = do
  type_t <- check styp defs ((name, Ann Typ (Slf name styp)) : ctx) -- todo: Ann
  match type_t Typ defs ctx
  return Typ
check (New styp expr) defs ctx = do
  let term_t = eval styp defs
  case term_t of
    (Slf sSame sStyp) -> do
      check term_t defs ctx
      term_T <- check expr defs ctx
      match term_T (subst sStyp (Ann term_t (New styp expr)) 0) defs ctx
      return styp
    otherwise ->
      Left "Non-self new."
check (Use expr) defs ctx = do
  expr_t <- check expr defs ctx
  case eval expr_t defs of
    (Slf sSame sStyp) -> do
      return (subst sStyp expr 0)
    otherwise ->
      Left "Non-self use."
check (Ref name) defs ctx = do
  return (fst (defs M.! name))
check (Ann ttyp tval) defs ctx = do
  return ttyp

code :: String
code =
  -- Identity
  "id    : {T : *} -> {x : T} -> T" ++
  "      = {T : *} => {x : T} => x;" ++

  -- Bool datatype
  "Bool  : *    = $self {P : {x : Bool} -> *} -> {t : (P True)} -> {f : (P False)} -> (P self);" ++
  "True  : Bool = &Bool {P : {x : Bool} -> *} => {t : (P True)} => {f : (P False)} => t;" ++
  "False : Bool = &Bool {P : {x : Bool} -> *} => {t : (P True)} => {f : (P False)} => f;" ++

  -- Not
  "not   : {x : Bool} -> Bool" ++
  "      = {x : Bool} => (((%x {s : Bool} => Bool) False) True);" ++

  -- And
  "and   : {x : Bool} -> {y : Bool} -> Bool" ++
  "      = {x : Bool} => {y : Bool} => (((%x {x : Bool} => Bool) (((%y {y : Bool} => Bool) True) False)) (((%y {y : Bool} => Bool) False) False));" ++

  -- Main
  "main  : Bool" ++
  "      = ((and True) False);"

main :: IO ()
main = do
  let defs = parse code
  let typ  = \ name -> fst (defs M.! name)
  let val  = \ name -> snd (defs M.! name)

  let main = val "main"

  putStrLn $ "Term: " ++ format (main) []
  putStrLn $ "Norm: " ++ format (eval main defs) []

  case check main defs [] of
    Right ty -> putStrLn $ "Type: " ++ format ty []
    Left err -> putStrLn err
