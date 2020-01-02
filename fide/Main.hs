module Main where

import           Control.Monad.State.Strict

import qualified Data.Map.Strict            as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import qualified System.Console.Haskeline   as H
import           System.Process             (callCommand)

import           Fide
import           Lang

import           Text.Megaparsec            hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

main :: IO ()
main = evalStateT fide (FideST M.empty)
