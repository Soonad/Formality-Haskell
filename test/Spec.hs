module Main where

import qualified Data.Vector.Unboxed as V
import           Data.Word

import           Test.Hspec
import           Test.QuickCheck

import           Runtime.Net

instance Arbitrary NType where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary Slot where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary Info where
  arbitrary = Info
    <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

prop_readInfo :: Info -> Bool
prop_readInfo l = l == (readInfoBits . infoBits) l

outCD :: Net
outCD =
  Net (V.fromList [(1,0,0,0),(1,1,1,1),(71,0,8,0),(71,0,9,0),(71,0,6,0),(71,0,7,0),(84,4,8,9),(164,5,8,9),(86,2,6,7),(166,3,6,7)])
    [0,1]
   []


outCC :: Net
outCC =
  Net (V.fromList [(1,0,0,0),(1,1,1,1),(87,0,4,0),(87,0,5,0),(87,0,2,0),(87,0,3,0)])
      [0,1]
      []

outCE :: Net
outCE =
  Net (V.fromList [(1,0,0,0),(87,0,1,0),(87,0,2,0)])
      [0]
      []


main :: IO ()
main = hspec $ do
  describe "Net.Node" $ do
    it "Info -> Bits -> Info is identity" $ do
      property $ prop_readInfo
  describe "Annihilation" $ do
    it "annihilates CON-CON" $ do
      reduce inCC `shouldBe` (outCC, 1)
  describe "Self-annihilation" $ do
    it "erases CON-ERA" $ do
      reduce inCE `shouldBe` (outCE, 1)
  describe "Duplication" $ do
    it "duplicates CON-DUP" $ do
      reduce inCD `shouldBe` (outCD, 1)

