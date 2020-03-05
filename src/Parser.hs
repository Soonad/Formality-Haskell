module Parser
  ( parseDefault
  , Parser.ParseError
  , module Lang
  , module Parser.Lang
  , module Parser.PreModule
  , module Parser.Types
  ) where

import           Data.Text              (Text)
import qualified Data.Text              as T
import qualified Data.Text.IO           as TIO
import           Data.Void

import           Text.Megaparsec        hiding (State)

import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy hiding (All)

import           Core                   (Eras (..), Name, Op (..))
import qualified Core                   as Core
import           Lang
import           Parser.Lang
import           Parser.PreModule
import           Parser.Types
import           Pretty

-- top level parser with default env and state
parseDefault :: Show a
             => Parser a
             -> Text
             -> Either (ParseErrorBundle Text Void) (a, ParseState, ())
parseDefault p s =
  runIdentity $ runParserT (runRWST p initParseEnv initParseState) "" s

-- a useful testing function
parserTest :: Show a => Parser a -> Text -> IO ()
parserTest p s = print $ parseDefault p s

fileTest :: Show a => Parser a -> FilePath -> IO ()
fileTest p f = do
  txt <- TIO.readFile f
  print $ parseDefault p txt

-- evals the term directly
--evalTest :: Parser Term -> Text -> IO ()
--evalTest p s = do
--  let Identity (Right (a,st,w)) = parseDefault p s
--  print $ a
--  print $ eval a Core.emptyModule

type ParseError = ParseErrorBundle Text Void
