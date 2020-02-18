{-# LANGUAGE FlexibleContexts #-}
module SimplerCore where

import           Data.Text                  (Text)
import qualified Data.Text                  as T
import Data.Equivalence.Monad

type Name = Text

data Term
  = Var Int
  | Typ
  | Val Int
  | Num
  | Lam Name Term Term
  | App Term Term
  | All Name Term Term
  | Mu Name Term
  | Any -- Type of any term
  | Rec Int
  | Slf Name Term
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

pretty :: Term -> Text
pretty t = go t [] []
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

maxFreeVar :: Term -> Int
maxFreeVar term = go term 0 where
  go term n = case term of
    Var i        -> if i < n then 0 else i-n
    All _ h b    -> go h n `max` go b (n + 1)
    Lam _ h b    -> go h n `max` go b (n + 1)
    App f a      -> go f n `max` go a n
    Slf _ t      -> go t (n + 1)
    Mu _ t       -> go t n
    _            -> 0

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

headForm :: Term -> Term
headForm term = case term of
  App f a -> case headForm f of
               Lam _ _ b -> headForm (substVar b a 0)
               f     -> App f a
  Mu _ _  -> headForm (unroll term)
  _       -> term

-- Evaluation ignoring the unrolling of terms. This is enough for contractible substitutions
eval :: Term -> Term
eval term = case term of
  All n h b -> All n (eval h) (eval b)
  Lam n h b -> Lam n (eval h) (eval b)
  App f a   ->
    let a' = eval a
    in case eval f of
      Lam _ _ b -> eval (substVar b a' 0)
      f            -> App f a'
  Mu n t    -> Mu n (eval t)
  Slf n t   -> Slf n (eval t)
  _         -> term

contractibleSubst :: Term -> Int -> Bool
contractibleSubst t n = case t of
  Var i     -> i /= n
  Mu _ t    -> contractibleSubst t (n + 1)
  Lam _ _ _ -> False 
  App _ _   -> False 
  _         -> True

-- The Lam and App cases could potentially be, instead
--  Lam _ t b -> contractibleSubst t n || contractibleSubst b (n + 1)
--  App f a   -> contractibleSubst f n || contractibleSubst a n
-- However, a contractible term T would lose the useful property that if it is normalized, then T^n is also normalized,
-- for any power n, where T^n means substitute variable 0 in T by itself n times, that is,
-- `T^0 = Var 0` and `T^(n+1) = subst T^n T 0`. This means in particular that if T is contractible,
-- then `Mu "X" T` is normalized no matter how many times we unroll it.


-- Examples of substitutions which are not contractible when you consider evaluation of terms, which rule out `Lam` and `App` as guards for recursion
notcontractible1 = Mu "X" (Lam "a" Typ (App (Rec 0) (Var 0)))
notcontractible2 = Mu "X" (App (Lam "a" Typ (Var 0)) (Rec 0))

isBohmRec :: Term -> Int -> Bool
isBohmRec t n = case t of
  Var i     -> i /= n
  Mu _ t    -> isBohmRec t (n + 1)
  _         -> True

isBohm :: Term -> Bool
isBohm t = case t of
  App f a   -> isBohm f && isBohm a
  Lam _ h b -> isBohm h && isBohm b
  All _ h b -> isBohm h && isBohm b
  Mu  _ t   -> isBohmRec t 0 && isBohm t
  Slf _ t   -> isBohm t
  _         -> True

evalBohm :: Term -> Term
evalBohm term = case term of
  All n h b -> All n (evalBohm h) (evalBohm b)
  Lam n h b -> Lam n (evalBohm h) (evalBohm b)
  App f a   -> case (evalBohm f, evalBohm a) of
    (Mu n t@(Lam _ _ _), Var i) -> App (Mu n t) (Var i)
    (Mu n t@(Lam _ _ _), Rec i) -> App (Mu n t) (Rec i)
    (Mu n t@(Lam _ _ _), a')    -> evalBohm $ App (substRec t (Mu n t) 0) a'
    (Lam _ _ b, a')             -> evalBohm (substVar b a' 0)
    (f', a')                    -> App f' a'
  Mu n t    -> Mu n (evalBohm t)
  Slf n t   -> Slf n (evalBohm t)
  _         -> term

-- Equality algorithm
eraseNames :: Term -> Term
eraseNames (App f a)   = App (eraseNames f) (eraseNames a)
eraseNames (Lam _ h b) = Lam "" (eraseNames h) (eraseNames b)
eraseNames (All _ h b) = All "" (eraseNames h) (eraseNames b)
eraseNames (Slf _ t)   = Slf "" (eraseNames t)
eraseNames (Mu  _ t)   = Mu  "" (eraseNames t)
eraseNames term        = term
  
data Node a = Stop | Continue a | Branch a a

sameNode :: Term -> Term -> Node (Term, Term)
sameNode (App f a) (App f' a')     = Branch (headForm f, headForm f') (headForm a, headForm a')
sameNode (Lam _ h b) (Lam _ h' b') = Branch (headForm h, headForm h') (headForm b, headForm b')
sameNode (All _ h b) (All _ h' b') = Branch (headForm h, headForm h') (headForm b, headForm b')
sameNode (Slf _ t) (Slf _ t')      = Continue (headForm t, headForm t')
sameNode _ _                       = Stop

equal :: Term -> Term -> Bool
equal term1 term2 = runEquivM' $ go [(headForm (eraseNames term1), headForm (eraseNames term2))] where
  go [] = return True
  go ((term1, term2) : pairs) = do
    b <- equivalent term1 term2
    if b
      then go pairs
      else
      case sameNode term1 term2 of
        Branch pair1 pair2 -> equate term1 term2 >> go (pair1 : pair2 : pairs)
        Continue pair -> equate term1 term2 >> go (pair : pairs)
        Stop -> return False

-- Examples
forall n = All n Typ
impl a b = All "" a (shiftVar b 1 0)

zero    = Lam "Z" Any (Lam "S" Any (Var 1))
suc     = Lam "n" Any (Lam "Z" Any (Lam "S" Any (App (Var 0) (Var 2))))
-- Both definitions of double are equal
double  = Mu "double" $ Lam "n" Any $ App (App (Var 0) zero) $ Lam "x" Any $ App suc $ App suc $ App (Rec 0) (Var 0)
double' = Lam "n" Any $ App (App (Var 0) zero) $ Mu "Rec" $  Lam "x" Any $ App suc $ App suc $ App (App (Var 0) zero) (Rec 0)

two  = App double $ App suc zero
five = App suc $ App double two
ten  = App suc $ App suc $ App suc $ App suc $ App suc $ five

-- The equality of the terms `typeF1` and `typeF2` takes a couple of seconds in the current (February 2020) JavaScript Formality implementation
-- but only takes a split second with the new equality algorithm
someTypeF = Lam "n" Any $ Lam "P" (impl Any Typ) $ App (Var 0) (Var 1)
typeF1     = App someTypeF (App double five)
typeF2     = App someTypeF ten
