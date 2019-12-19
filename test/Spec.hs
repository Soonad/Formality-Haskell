module Main where

import           Test.Hspec
import           Test.QuickCheck

import           Spec.Net  as Net
import           Spec.Lang as Lang


main :: IO ()
main = hspec $ do
  describe "Net" $ Net.spec
  describe "Lang" $ Lang.spec
