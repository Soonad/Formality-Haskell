module Parser.PreModule where

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Text                  (Text)
import qualified Data.Text                  as T

import           Data.Set                   (Set)
import qualified Data.Set                   as Set

import           Control.Monad.RWS.Lazy     hiding (All)

import Lang
import Parser.Types
import Parser.Lang

declaration :: Parser Declaration
declaration = choice
  [ try $ definition
  , try $ enum
  , try $ datatype
  , try $ import_
  ]

definition :: Parser Declaration
definition = do
  (n,t) <- def (optional $ sym ";")
  return $ Expr n t

enum :: Parser Declaration
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

datatype :: Parser Declaration
datatype = do
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

import_ :: Parser Declaration
import_ = do
  sym "import"
  n <- name
  h <- maybe "" id <$> optional (sym "#" >> some (satisfy isFileID))
  return $ Impt n (T.pack h)
  where
    isFileID x = elem x (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'])

premodule :: Parser [Declaration]
premodule = sc >> decls
  where
    decls :: Parser [Declaration]
    decls = (sc >> eof >> return []) <|> next

    next :: Parser [Declaration]
    next = do
     d  <- declaration <* sc
     case d of
         Expr n t -> do
           ds <- decls
           return $ d : ds
         Enum ns -> do
           ds <- decls
           return $ d : ds
         Data n _ _ cs -> do
           let cns = (\(Ctor n _ _) -> n) <$> cs
           ds <- decls
           return $ d : ds
         Impt _ _ -> do
           ds <- decls
           return $ d : ds

