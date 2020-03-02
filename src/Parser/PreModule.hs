module Parser.PreModule where

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Text                  (Text)
import qualified Data.Text                  as T
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import           Data.Set                   (Set)
import qualified Data.Set                   as Set

import           Control.Monad.RWS.Lazy     hiding (All)

import Lang
import Core (Name)
import Parser.Types
import Parser.Lang

declaration :: Parser Declaration
declaration = choice
  [ try $ definition
  , try $ enum
  , try $ Data <$> datatype
  , try $ import_
  ]

definition :: Parser Declaration
definition = do
  (n,t) <- def (optional $ sym ";")
  names n
  return $ Expr n t

enum :: Parser Declaration
enum = do
  sym "enum"
  Enum <$> some e
  where
    e = do
      sym "|"
      n <- name
      names n
      sc
      return n

datatype :: Parser ADT
datatype = do
  n <- sym "T" >> name
  names n
  ps <- optional' $ binds False "{" "}"
  sc
  is <- optional' $ binders ((\(x,y,z) -> VarB x) <$> ps) (binds False "(" ")")
  sc
  cs <- binders ((\(x,y,z) -> VarB x) <$> ps) (many (sym "|" >> ctor))
  return $ ADT n (f <$> ps) (f <$> is) (M.fromList cs)
  where
  f (a,b,c) = (a,b)

  optional' :: Parser [a] -> Parser [a]
  optional' p = maybe [] id <$> (optional p)

  ctor :: Parser (Name, Ctor)
  ctor = do
    n  <- name
    names n
    ps <- optional' (binds True "(" ")") <* sc
    ix <- optional (sym ":" >> binders ((\(x,y,z) -> VarB x) <$> ps) term <* sc)
    return $ (n, Ctor (f <$> ps) ix)

import_ :: Parser Declaration
import_ = do
  sym "import"
  n <- name
  h <- maybe "" id <$> optional (sym "#" >> some (satisfy isFileID))
  return $ Impt n (T.pack h)
  where
    isFileID x = elem x (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'])

seekADT :: Parser ADT
seekADT = datatype <|> (takeP Nothing 1 >> seekADT)

premodule :: Parser [Declaration]
premodule = do
  adts <- lookAhead $ many $ try seekADT
  sequence $ adtCtors <$> adts
  sc >> decls
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
         Data (ADT _ _ _ cs) -> do
           let cns = M.keys cs
           ds <- decls
           return $ d : ds
         Impt _ _ -> do
           ds <- decls
           return $ d : ds

