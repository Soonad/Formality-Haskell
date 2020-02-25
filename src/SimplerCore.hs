{-# LANGUAGE FlexibleContexts #-}
module SimplerCore where

import Control.Applicative (liftA2)

import           Data.Equivalence.Monad
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as I (putStrLn)
import           Data.Sequence (Seq(..))
import qualified Data.Sequence as S

type Name = Text

data Dir  = Lft | Rgt | Ctr deriving (Eq, Show, Ord)
type Path = Seq Dir

data Term
  = Var Int
  | Rec Int
  | App Term Term
  | Lam Name Term Term
  | All Name Term Term
  | Slf Name Term
  | Mu  Name Term
  | Any
  | Typ
  | Num
  | Val Int
  -- The following should only be used by the equality algorithm
  | Bound Path
  | Free Int
  deriving (Eq, Show, Ord)

hasFreeVar :: Term -> Int -> Bool
hasFreeVar term n = case term of
  Var i        -> i == n
  All _ h b    -> hasFreeVar h n || hasFreeVar b (n + 1)
  Lam _ h b    -> hasFreeVar h n || hasFreeVar b (n + 1)
  App f a      -> hasFreeVar f n || hasFreeVar a n
  Slf _ t      -> hasFreeVar t (n + 1)
  Mu  _ t      -> hasFreeVar t n
  _            -> False

pretty :: Term -> IO ()
pretty t = I.putStrLn $ go t [] []
  where
    show' = T.pack . show
    cat   = T.concat

    go :: Term -> [Text] -> [Text] -> Text
    go t vs rs = case t of
      Var i                     -> if i < length vs then vs !! i else cat ["^", show' (i - length vs)]
      Rec i                     -> if i < length rs then rs !! i else cat ["#", show' (i - length rs)]
      Typ                       -> "Type"
      All n h@Typ b             -> cat ["∀(", n, "). ", go b (n : vs) rs]
      All n h@(All _ _ _) b     -> if hasFreeVar b 0 then cat ["(", n, " : ", go h vs rs, ") -> ", go b (n : vs) rs] else cat ["(", go h vs rs, ") -> ", go b (n : vs) rs]
      All n h b                 -> if hasFreeVar b 0 then cat ["(", n, " : ", go h vs rs, ") -> ", go b (n : vs) rs] else cat [go h vs rs, " -> ", go b (n : vs) rs]
      Lam n h@Any b@(Lam _ _ _) -> cat ["(", n, ", ", T.tail $ go b (n : vs) rs]
      Lam n h@Any b             -> cat ["(", n, ") => ", go b (n : vs) rs]
      Lam n h b@(Lam _ _ _)     -> cat ["(", n, " : ", go h vs rs, ", ", T.tail $ go b (n : vs) rs]
      Lam n h b                 -> cat ["(", n, " : ", go h vs rs, ") => ", go b (n : vs) rs]
      App f@(App _ _) a         ->
        cat [T.init $ go f vs rs, " ", go a vs rs, ")"]
      App f@(Lam _ _ _) a       ->
        cat ["((", go f vs rs, ") " , go a vs rs, ")"]
      App f@(Mu _ _) a          ->
        cat ["((", go f vs rs, ") " , go a vs rs, ")"]
      App f a                   -> cat ["(", go f vs rs, " ", go a vs rs, ")"]
      Slf n t                   -> cat ["${", n, "} (", go t (n : vs) rs, ")"]
      Mu n t                    -> cat ["μ(", n, "). ", go t vs (n : rs)]
      Num                       -> "Number"
      Val i                     -> show' i
      Any                       -> "Any"
      Free i                    -> cat ["Free(", show' i, ")"]
      Bound ps                  -> cat ["Bound(", T.pack $ show ps, ")"]

shiftVar :: Term -> Int -> Int -> Term
shiftVar term inc dep = case term of
  Var i     -> Var (if i < dep then i else (i + inc))
  All n h b -> All n (shiftVar h inc dep) (shiftVar b inc (dep + 1))
  Lam n h b -> Lam n (shiftVar h inc dep) (shiftVar b inc (dep + 1))
  App f a   -> App (shiftVar f inc dep) (shiftVar a inc dep)
  Slf n t   -> Slf n (shiftVar t inc (dep + 1))
  Mu  n t   -> Mu  n (shiftVar t inc dep)
  x         -> x

shiftRec :: Term -> Int -> Int -> Term
shiftRec term inc dep = case term of
  Lam n h b -> Lam n (shiftRec h inc dep) (shiftRec b inc dep)
  All n h b -> All n (shiftRec h inc dep) (shiftRec b inc dep)
  App f a   -> App (shiftRec f inc dep) (shiftRec a inc dep)
  Mu  n t   -> Mu  n (shiftRec t inc (dep + 1))
  Slf n t   -> Slf n (shiftRec t inc dep)
  Rec i     -> Rec (if i < dep then i else (i + inc))
  x         -> x

substVar :: Term -> Term -> Int -> Term
substVar term v dep  = case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  All n h b   -> All n (substVar h v dep) (substVar b vV (dep + 1))
  Lam n h b   -> Lam n (substVar h v dep) (substVar b vV (dep + 1))
  App f a     -> App (substVar f v dep) (substVar a v dep)
  Mu  n t     -> Mu  n (substVar t vR dep)
  Slf n t     -> Slf n (substVar t vV (dep + 1))
  x           -> x
  where
    vV = shiftVar v 1 0
    vR = shiftRec v 1 0

substRec :: Term -> Term -> Int -> Term
substRec term v dep = case term of
  All n h b   -> All n (substRec h v dep) (substRec b vV dep)
  Lam n h b   -> Lam n (substRec h v dep) (substRec b vV dep)
  App f a     -> App (substRec f v dep) (substRec a v dep)
  Mu  n t     -> Mu  n (substRec t vR (dep + 1))
  Slf n t     -> Slf n (substRec t vV dep)
  Rec i       -> if i == dep then v else Rec (i - if i > dep then 1 else 0)
  x           -> x
  where
    vV = shiftVar v 1 0
    vR = shiftRec v 1 0

substManyVar :: Term -> [Term] -> Int -> Term
substManyVar t vals d = go t vals d 0
  where
    l = length vals - 1
    go t (v:vs) d i =
      go (substVar t (shiftVar v (l - i) 0) (d + l - i)) vs d (i + 1)
    go t [] d i = t

unroll :: Term -> Term
unroll term = case term of
  All n h b -> All n (unroll h) (unroll b)
  Lam n h b -> Lam n (unroll h) (unroll b)
  App f a   -> App (unroll f) (unroll a)
  Mu n t    -> substRec t (Mu n t) 0
  Slf n t   -> Slf n (unroll t)
  _         -> term

untelescope :: Term -> [Term] -> Term
untelescope term [] = term
untelescope term (a : as) = untelescope (App term a) as

headFormPlus :: Term -> Term
headFormPlus term = go term [] where
  go term apps = case term of
    App f a   -> go f (a : apps)
    Lam n h b  -> case apps of
                    []       -> Lam n h b
                    (a : as) -> go (substVar b a 0) as
    Mu _ t    -> go (unroll term) (map headFormPlus apps)
    _         -> untelescope term apps

-- Evaluation ignoring the unrolling of terms. This is enough for contractible substitutions
evalNoMu :: Term -> Term
evalNoMu term = case term of
  All n h b -> All n (evalNoMu h) (evalNoMu b)
  Lam n h b -> Lam n (evalNoMu h) (evalNoMu b)
  App f a   ->
    let a' = evalNoMu a
    in case evalNoMu f of
      Lam _ _ b -> evalNoMu (substVar b a' 0)
      f            -> App f a'
  Mu n t    -> Mu n (evalNoMu t)
  Slf n t   -> Slf n (evalNoMu t)
  _         -> term

-- Equality algorithm
freeUnboundVars :: Term -> Term
freeUnboundVars t = go t 0 where
  go t dep = case t of
    Var i     -> if i < dep then Var i else Free (i - dep)
    Lam n h b -> Lam n (go h dep) (go b (dep + 1))
    All n h b -> All n (go h dep) (go b (dep + 1))
    App f a   -> App (go f dep) (go a dep)
    Slf n b   -> Slf n (go b (dep + 1))
    Mu  n t   -> Mu  n (go t dep)
    x         -> x

equivalentTerms term1 term2 = do
  e <- equivalent term1 term2
  if e
    then return True
    else
    case (term1, term2) of
      (Lam _ _ b, Lam _ _ b')  -> equivalentTerms b b'
      (App f a, App f' a')     -> liftA2 (&&) (equivalentTerms f f') (equivalentTerms a a')
      (All _ h b, All _ h' b') -> liftA2 (&&) (equivalentTerms h h') (equivalentTerms b b')
      (Mu _ t, Mu _ t')        -> equivalentTerms t t'
      (Slf _ t, Slf _ t')      -> equivalentTerms t t'
      (_, _)                   -> return False

data Node a = Stop | Continue a | Branch a a

sameNode :: Term -> Term -> Path -> Node (Term, Term, Path)
sameNode (App f a) (App f' a')     ps = Branch (headFormPlus f, headFormPlus f', ps :|> Lft) (headFormPlus a, headFormPlus a', ps :|> Rgt)
sameNode (Lam _ h b) (Lam _ h' b') ps = Branch (headFormPlus h, headFormPlus h', ps :|> Lft) (headFormPlus $ substVar b (Bound ps) 0, headFormPlus $ substVar b' (Bound ps) 0, ps :|> Rgt)
sameNode (All _ h b) (All _ h' b') ps = Branch (headFormPlus h, headFormPlus h', ps :|> Lft) (headFormPlus $ substVar b (Bound ps) 0, headFormPlus $ substVar b' (Bound ps) 0, ps :|> Rgt)
sameNode (Slf _ t) (Slf _ t')      ps = Continue (headFormPlus $ substVar t (Bound ps) 0, headFormPlus $ substVar t' (Bound ps) 0, ps :|> Ctr)
sameNode _ _                       ps = Stop

equal :: Term -> Term -> Bool
equal term1 term2 = runEquivM' $ go (S.singleton (headFormPlus $ freeUnboundVars term1, headFormPlus $ freeUnboundVars term2, Empty)) where
  go Empty = return True
  go ((term1, term2, ps) :<| tris) = do
    b <- equivalentTerms term1 term2
    equate term1 term2
    if b
      then go tris
      else
      case sameNode term1 term2 ps of
        Branch tri1 tri2 -> go (tris :|> tri1 :|> tri2)
        Continue tri -> go (tris :|> tri)
        Stop -> return False

---- Examples
forall n = All n Typ
impl a b = All "" a (shiftVar b 1 0)

-- Fixpoint Combinator
fix = Lam "f" Any $ App (Lam "x" Any $ App (Var 1) $ App (Var 0) (Var 0)) (Lam "x" Any $ App (Var 1) $ App (Var 0) (Var 0))

-- Scott encoded natural number constructors
zero    = Lam "Z" Any (Lam "S" Any (Var 1))
suc     = Lam "n" Any (Lam "Z" Any (Lam "S" Any (App (Var 0) (Var 2))))

-- All the following definitions of double are equal
double   = Mu "double" $ Lam "n" Any $ App (App (Var 0) zero) $ Lam "x" Any $ App suc $ App suc $ App (Rec 0) (Var 0)
double'  = Lam "n" Any $ App (App (Var 0) zero) $ Mu "Rec" $  Lam "x" Any $ App suc $ App suc $ App (App (Var 0) zero) (Rec 0)
double'' = App fix $ Lam "double" Any $ Lam "n" Any $ App (App (Var 0) zero) $ Lam "x" Any $ App suc $ App suc $ App (Var 2) (Var 0)

one   = App suc zero
two   = App suc one
three = App suc two
four  = App double two
five  = App suc $ four
ten   = App suc $ App suc $ App suc $ App suc $ App suc five

-- The equality of the terms `typeF1` and `typeF2` takes a couple of seconds in the current (February 2020) JavaScript Formality implementation
-- but only takes a split second with the new equality algorithm
typeF0 = Lam "n" Any $ Lam "P" (impl Any Typ) $ App (Var 0) (Var 1)
typeF1     = App typeF0 (App double five)
typeF2     = App typeF0 ten

-- also, the JS version is not able to prove that the following are equal
regularType1  = Mu "X" $ impl Any $ impl Any (Rec 0)
regularType2 = impl Any $ Mu "X" $ impl Any $ impl Any (Rec 0)

-- neither can it prove that `regularType4` is equivalent to `regularType3` after reduction
regularType3 = Lam "A" Typ $ Mu "X" $ impl (Var 0) (Rec 0)
regularType4 = Mu "X" $ Lam "A" Typ $ impl (Var 0) (App (Rec 0) (Var 0))

-- The algorithm also works on irregular terms
someFunc    = Lam "n" Any $ App (App (Var 0) zero) (Lam "pred" Any (Var 1))
someTypeF   = Mu  "X" $ Lam "A" Any $ Lam "n" Any $ impl (App (Var 1) (App someFunc (Var 0))) $ App (App (Rec 0) (Var 1)) (App suc (Var 0))
-- the first two are equal terms
someType1  = Lam "A" Any $ App (App someTypeF (Var 0)) zero
someType2  = Lam "A" Any $ impl (App (Var 0) zero) $ impl (App (Var 0) one) $ impl (App (Var 0) two) $ impl (App (Var 0) three) $ App (App someTypeF (Var 0)) four
-- the algorithm is quickly able to check that the following is not equal to either of the last two terms, while in the JS version it takes a couple of seconds
someType3 = Lam "" Any $ impl (App (Var 0) zero) $ impl (App (Var 0) one) $ impl (App (Var 0) two) $ impl (App (Var 0) three) $ App (App someTypeF (Var 0)) three
notEq = equal someType1 someType3

-- Bool type
boolConstructor  b t f = Slf "self" $ All "P" (impl b Typ) $ impl (App (Var 0) t) $ impl (App (Var 0) f) $ App (Var 0) (Var 1)
trueConstructor  b t f = Lam "P" (impl b Typ) $ Lam "case_true" (App (Var 0) t) $ Lam "case_false" (App (Var 1) f) (Var 1)
falseConstructor b t f = Lam "P" (impl b Typ) $ Lam "case_true" (App (Var 0) t) $ Lam "case_false" (App (Var 1) f) (Var 0)

bool  = Mu "Bool"  $ boolConstructor (Rec 0)
  (Mu "true"  $ trueConstructor  (Rec 1) (Rec 0) (Mu "false" $ falseConstructor (Rec 2) (Rec 1) (Rec 0)))
  (Mu "false" $ falseConstructor (Rec 1) (Mu "true"  $ trueConstructor  (Rec 2) (Rec 0) (Rec 1)) (Rec 0))
true  = Mu "True"  $ trueConstructor  bool (Rec 0) (Mu "false" $ falseConstructor bool (Rec 1) (Rec 0))
false = Mu "False" $ falseConstructor bool true (Rec 0)

boolEq  = equal bool  (boolConstructor  bool true false)
trueEq  = equal true  (trueConstructor  bool true false)
falseEq = equal false (falseConstructor bool true false)
