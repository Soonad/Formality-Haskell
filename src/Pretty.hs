module Pretty where

import           Data.Text                  (Text)
import qualified Data.Text                  as T

import Core

-- pretty-printing
pretty :: Term -> Text
pretty t = go t []
  where
    show' = T.pack . show
    cat   = T.concat

    showOp ADD = " + "
    showOp SUB = " - "
    showOp MUL = " * "
    showOp DIV = " / "
    showOp MOD = " % "

    go :: Term -> [Text] -> Text
    go t s = case t of
      Var i          -> if i < length s then s !! i else cat ["^", show' i]
      Typ            -> "Type"
      All n h Eras b -> cat ["(", n, " : ", go h s, ";) -> ", go b (n : s)]
      All n h e b    -> cat ["(", n, " : ", go h s, ") -> ", go b (n : s)]
      Lam n h Eras b -> cat ["(", n, " : ", go h s, ";) => ", go b (n : s)]
      Lam n h e b    -> cat ["(", n, " : ", go h s, ") => ", go b (n : s)]
      App f@(Lam _ _ _ _) a Eras ->
                        cat ["((", go f s, ") " , go a s, ";)"]
      App f@(Lam _ _ _ _) a e    ->
                        cat ["((", go f s, ") " , go a s, ")"]
      App f a Eras   -> cat ["(", go f s, " " , go a s, ";)"]
      App f a e      -> cat ["(", go f s, " ", go a s, ")"]
      Let bs b       ->
        let bs' = (\(n,t) -> cat [n, " = ", go t s, ";"]) <$> bs in
        cat (["let "] ++ bs' ++ [go b s])
      Slf n t        -> cat ["${", n, "}", go t s]
      New t x        -> cat ["new(", go t s, ")", go x s]
      Use x          -> cat ["use(", go x s, ")"]
      Num            -> "Number"
      Val i          -> show' i
      Op2 o a b      -> cat [go a s, showOp o, go b s]
      Op1 o a b      -> cat [show' a, showOp o, go b s]
      Ite c t f      -> cat ["if ", go c s, " then ", go t s, " else ", go f s]
      Ann x y        -> cat [go y s, " :: ", go x s]
      Log x y        -> cat ["log(", go x s, "); ", go y s]
      Hol n          -> cat ["?", n]
      Ref n i        -> cat [n , "#", show' i]

