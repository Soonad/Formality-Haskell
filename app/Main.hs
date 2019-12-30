{-# LANGUAGE FlexibleContexts #-}
module Main where

import           Control.Monad.State.Strict

import qualified Data.Map.Strict            as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import qualified System.Console.Haskeline   as H
import           System.Process             (callCommand)

import           Fide


main :: IO ()
main = evalStateT fide M.empty


