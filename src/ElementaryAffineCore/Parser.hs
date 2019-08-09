{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds         #-}
-- |
-- Module      : ElementaryAffineCore.Parser
-- Copyright   : [2019] Sunshine Cybernetics
-- License     : MIT
--
-- Maintainer  : Sunshine Cybernetics
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Parsing of the Elementary Affine Core files.
-- Here we forming the blank for further processing (substituting etc.)

module ElementaryAffineCore.Parser
   (topExpressions) where

import Data.Text (Text, pack, unpack)
import Data.Void (Void)
import Text.Megaparsec
  ( Parsec, SourcePos(..), between, choice, chunk, getSourcePos, many
  , oneOf, skipSome, some , someTill, try, (<|>), eof, skipMany)
import Text.Megaparsec.Char (char, newline, space1, string)

import qualified Data.Map as M
import qualified Text.Megaparsec.Char.Lexer as L

import ElementaryAffineCore.Types

type Parser = Parsec Void Text
type RTerm = Term 'Raw
type RExp = Expression 'Raw

-- | Spaces and comments consumer.
scc :: Parser ()
scc = L.space (space1 <|> skipSome newline) lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "/"
    blockCmnt = L.skipBlockComment "/*" "*/"

lexeme
  :: Parser a
  -> Parser a
lexeme = L.lexeme scc

symbol
  :: Text
  -> Parser Text
symbol = L.symbol scc

-- | Lexed string. It consumes spaces and newlines after a string.
lString
  :: Text
  -> Parser Text
lString = lexeme . string

parens
  :: Parser a
  -> Parser a
parens = between (symbol "(") (symbol ")")

curlyBrackets
  :: Parser a
  -> Parser a
curlyBrackets = between (symbol "{") (symbol "}")

symb :: Parser Text
symb = lexeme $ do
    txt <- pack <$> some (oneOf $ ['a'..'z'] ++ ['A' .. 'Z'])
    if txt `elem` rsWords
    then fail $ unpack $ "Keyword \"" <> txt <> "\" cannot be used as definition."
    else return txt

-- | Reserved words.
rsWords :: [Text]
rsWords = ["dup", "def"]

 -- | Parser of a term.
term_
  :: [Text]
  -> Parser RTerm
term_ vars = lexeme $ choice
             [ app_ vars
             , lam_ vars
             , put_ vars
             , dup_ vars
             , var_ vars
             ]

-- | Parser of an expression. All unkown strings are parsed as links to terms.
-- During the substitution all links without corresponding term will be marked
-- as free variables.
expression
  :: [Text]
  -> Parser RExp
expression vars = lexeme $ do
    pos  <- getSourcePos
    env  <- let_ vars <|> return M.empty
    (term_ vars >>= \term -> return $ ExpRaw pos term env) <|>
      (symb >>= \ref -> return $ ExpRaw pos (Reference ref) env)

-- | Name of a top-level expression.
topExpName :: Parser Text
topExpName = lexeme $ between (lString "def") (symbol ":") symb

topExpression :: Parser (Text,RExp)
topExpression = lexeme $ (,) <$> topExpName <*> expression []

topExpressions :: Parser (Environment 'Raw)
topExpressions = M.fromList <$> (scc *> lexeme (someTill topExpression eof))

-- Parsers of the specific terms

let_
  :: [Text]
  -> Parser (Environment 'Raw)
let_ vars = lexeme $ do
    exps <- some $ (,) <$> between (lString "let") (symbol ":") symb <*>
        expression vars
    return $ M.fromList exps

put_
  :: [Text]
  -> Parser RTerm
put_ vars = do
    char '#'
    term <- (try $ expression vars) <|> parens (expression vars)
    return $ Put term

app_
  :: [Text]
  -> Parser RTerm
app_ vars = parens $ do
    term1 <- expression vars
    term2 <- expression vars
    return $ App term1 term2

lam_
  :: [Text]
  -> Parser RTerm
lam_ oldVars = lexeme $ do
    var <- curlyBrackets symb
    exp  <- expression (var : oldVars)
    return $ Lam (Variable var) exp

-- | We parse only bounded or duplicated variables. All other variables are parsed as links to terms.
-- They will be marked as variables during the substitution phase.
var_
  :: [Text]
  -> Parser RTerm
var_ vars = lexeme (Var . Variable <$> choice (map chunk vars))

dup_
  :: [Text]
  -> Parser RTerm
dup_ vars = lexeme $ do
    lString "dup"
    var <- symb
    lString "="
    term1 <- expression vars
    lexeme $ symbol ";"
    term2 <- expression (var : vars)
    return $ Dup (Variable var) term1 term2
