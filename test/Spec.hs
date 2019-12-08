module Main where

import qualified Data.Vector.Unboxed as V
import           Data.Word

import           Test.Hspec
import           Test.QuickCheck

import           Runtime.INet
import           Runtime.INode

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
outCD= Net
  (V.fromList $
    [ mkFree 0
    , mkFree 1
    , mkNode Con M 1 L 2 L 3
    , mkNode Dup M 0 L 4 L 5
    , mkSet L 0
    , mkSet R 0
    , mkSet L 1
    , mkSet R 1
    ])
  [0,1]
  []


main :: IO ()
main = hspec $ do
  describe "Net.Node" $ do
    it "Info -> Bits -> Info is identity" $ do
      property $ prop_readInfo
--  describe "Annihilation" $ do
--    it "annihilates CON-CON" $ do
--      reduce inConCon `shouldBe` (outConCon, 1)
--    it "annihilates DUP-DUP" $ do
--      reduce inDupDup `shouldBe` (outDupDup, 1)
--  describe "Self-annihilation" $ do
--    it "erases CON-ERA" $ do
--      reduce inConEra `shouldBe` (outZE, 1)
  describe "Duplication" $ do
    it "duplicates CON-DUP" $ do
      reduce inCD `shouldBe` (outCD, 1)



-- CON(a)-CON(a)
--inZaZa :: Net
--inZaZa= makeNet
--  [ Node Z 0 (Ptr 1 P) (Ptr 2 L) (Ptr 2 R) 0
--  , Node Z 0 (Ptr 0 P) (Ptr 3 L) (Ptr 3 R) 0
--  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
--  , Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0
--  ]
--
--outZaZa :: Net
--outZaZa = Net nodes [0,1] [] where
--  nodes = M.fromList $
--    [ (2, Node Z 0 Free (Ptr 3 L) (Ptr 3 R) 0)
--    , (3, Node Z 0 Free (Ptr 2 L) (Ptr 2 R) 0)
--    ]
--
---- CON(a)-CON(b)
--zaZb :: Net
--zaZb = makeNet
--  [ Node Z 0 (Ptr 1 P) Free Free 0
--  , Node Z 1 (Ptr 0 P) Free Free 0
--  ]
--
---- OP1-OP1
--inUU :: Net
--inUU = makeNet
--  [ Node U 0 (Ptr 1 P) (Ptr 2 L) Free 2
--  , Node U 0 (Ptr 0 P) (Ptr 3 L) Free 2
--  , Node Z 0 Free (Ptr 0 L) Free 0
--  , Node Z 0 Free (Ptr 1 L) Free 0
--  ]
--
--outUU :: Net
--outUU = Net nodes [0,1] [] where
--  nodes = M.fromList $
--    [ (2, Node Z 0 Free (Ptr 3 L) Free 0)
--    , (3, Node Z 0 Free (Ptr 2 L) Free 0)
--    ]
--
---- OP2-OP2
--inBB :: Net
--inBB = makeNet
--  [ Node B 0 (Ptr 1 P) (Ptr 2 L) (Ptr 2 R) 0
--  , Node B 0 (Ptr 0 P) (Ptr 3 L) (Ptr 3 R) 0
--  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
--  , Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0
--  ]
--
--outBB :: Net
--outBB = Net nodes [0,1] [] where
--  nodes = M.fromList $
--    [ (2, Node Z 0 Free (Ptr 3 L) (Ptr 3 R) 0)
--    , (3, Node Z 0 Free (Ptr 2 L) (Ptr 2 R) 0)
--    ]
--
---- ITE-ITE
--inII :: Net
--inII = makeNet
--  [ Node I 0 (Ptr 1 P) (Ptr 2 L) (Ptr 2 R) 0
--  , Node I 0 (Ptr 0 P) (Ptr 3 L) (Ptr 3 R) 0
--  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
--  , Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0
--  ]
--
--outII :: Net
--outII = Net nodes [0,1] [] where
--  nodes = M.fromList $
--    [ (2, Node Z 0 Free (Ptr 3 L) (Ptr 3 R) 0)
--    , (3, Node Z 0 Free (Ptr 2 L) (Ptr 2 R) 0)
--    ]
--
---- NUM-NUM
--inNN :: Net
--inNN = makeNet
--  [ Node N 0 (Ptr 1 P) Free Free 2
--  , Node N 0 (Ptr 0 P) Free Free 2
--  ]
--
--outNN :: Net
--outNN = Net nodes [0,1] [] where
--  nodes = M.empty
--
---- CON-ERA
--inZE :: Net
--inZE = makeNet
--  [ Node Z 0 (Ptr 0 P) (Ptr 1 L) (Ptr 1 R) 0
--  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
--  ]
--
--outZE :: Net
--outZE = Net nodes [0] [] where
--  nodes = M.fromList
--    [(1, Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0)]
--
---- OP1-ERA
--inUE :: Net
--inUE = makeNet
--  [ Node U 0 (Ptr 0 P) (Ptr 1 L) Free 1
--  , Node Z 0 Free (Ptr 0 L) Free 0
--  ]
--
--outUE :: Net
--outUE = Net nodes [0] [] where
--  nodes = M.fromList
--    [(1,Node Z 0 Free (Ptr 1 L) Free 0)]
--
--
---- OP2-ERA
--inBE :: Net
--inBE = makeNet
--  [ Node B 0 (Ptr 0 P) (Ptr 1 L) (Ptr 1 R) 0
--  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
--  ]
--
--outBE :: Net
--outBE =  Net nodes [0] [] where
--  nodes = M.fromList
--    [(1,Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0)]
--
---- ITE-ERA
--inIE :: Net
--inIE = makeNet
--  [ Node I 0 (Ptr 0 P) (Ptr 1 L) (Ptr 1 R) 0
--  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
--  ]
--
--outIE :: Net
--outIE =  Net nodes [0] [] where
--  nodes = M.fromList
--    [(1,Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0)]
--
--inNE :: Net
--inNE = makeNet
--  [ Node U 0 (Ptr 0 P) Free Free 1
--  ]
--
--outNE :: Net
--outNE = Net nodes [0] [] where
--  nodes = M.empty
