module Main where

import           Test.Hspec
import           Test.QuickCheck

import           Spec.Net  as Net
import           Spec.Parser as Parser
import           Spec.Core  as Core


main :: IO ()
main = hspec $ do
 -- describe "Net"  $ Net.spec
  describe "Parser" $ Parser.spec
  describe "Core" $ Core.spec
