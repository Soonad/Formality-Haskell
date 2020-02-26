module Spec.Parser.Utils where

import           Data.Text                  (Text)
import qualified Data.Text                  as T

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Control.Monad.RWS.Lazy    hiding (All)
import           Parser

parse' :: Show a => Parser a -> Text -> Maybe a
parse' p s = either (const Nothing) (\(a, st, w) -> Just a) (parseDefault p s)
