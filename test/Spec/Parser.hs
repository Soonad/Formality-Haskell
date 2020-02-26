module Spec.Parser where

import           Test.Hspec
import           Test.QuickCheck

import           Spec.Parser.Lang      as Lang
import           Spec.Parser.PreModule as PreModule

spec :: SpecWith ()
spec = do
  describe "Lang" $ Lang.spec
  describe "PreModule" $ PreModule.spec
