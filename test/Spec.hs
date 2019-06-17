module Main where

import qualified Data.Map.Strict as M
import           FormalityNet
import           Test.Hspec

main :: IO ()
main = hspec $ do
  describe "Annihilation" $ do
    it "annihilates CON-CON with a == b" $ do
      reduce inZaZa `shouldBe` (outZaZa, 1)
    it "annihilates OP1-OP1" $ do
      reduce inUU `shouldBe` (outUU, 1)
    it "annihilates OP2-OP2" $ do
      reduce inBB `shouldBe` (outBB, 1)
    it "annihilates ITE-ITE" $ do
      reduce inII `shouldBe` (outII, 1)
    it "annihilates NUM-NUM" $ do
      reduce inNN `shouldBe` (outNN, 1)
  describe "Self-annihilation" $ do
    it "erases CON-ERA" $ do
      reduce inZE `shouldBe` (outZE, 1)
    it "erases OP1-ERA" $ do
      reduce inUE `shouldBe` (outUE, 1)
    it "erases OP2-ERA" $ do
      reduce inBE `shouldBe` (outBE, 1)
    it "erases ITE-ERA" $ do
      reduce inIE `shouldBe` (outIE, 1)
    it "erases NUM-ERA" $ do
      reduce inNE `shouldBe` (outNE, 1)
--  describe "Duplication" $ do
--    it "duplicates CON-CON with a /= b" $ do
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates CON-OP2"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates CON-ITE"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates CON-NUM"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--  describe "Duplication (half)" $ do
--    it "duplicates CON-OP1"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates OP1-OP2"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates OP1-ITE"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--  describe "Numeric" $ do
--    it "duplicates OP1-NUM"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates OP2-NUM"
--      reduce inZaZa `shouldBe` (outZaZa, 1)
--    it "duplicates ITE-NUM"
--      reduce inZaZa `shouldBe` (outZaZa, 1)



-- CON(a)-CON(a)
inZaZa :: Net
inZaZa= makeNet
  [ Node Z 0 (Ptr 1 P) (Ptr 2 L) (Ptr 2 R) 0
  , Node Z 0 (Ptr 0 P) (Ptr 3 L) (Ptr 3 R) 0
  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
  , Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0
  ]

outZaZa :: Net
outZaZa = Net nodes [0,1] [] where
  nodes = M.fromList $
    [ (2, Node Z 0 Free (Ptr 3 L) (Ptr 3 R) 0)
    , (3, Node Z 0 Free (Ptr 2 L) (Ptr 2 R) 0)
    ]

-- CON(a)-CON(b)
zaZb :: Net
zaZb = makeNet
  [ Node Z 0 (Ptr 1 P) Free Free 0
  , Node Z 1 (Ptr 0 P) Free Free 0
  ]

-- OP1-OP1
inUU :: Net
inUU = makeNet
  [ Node U 0 (Ptr 1 P) (Ptr 2 L) Free 2
  , Node U 0 (Ptr 0 P) (Ptr 3 L) Free 2
  , Node Z 0 Free (Ptr 0 L) Free 0
  , Node Z 0 Free (Ptr 1 L) Free 0
  ]

outUU :: Net
outUU = Net nodes [0,1] [] where
  nodes = M.fromList $
    [ (2, Node Z 0 Free (Ptr 3 L) Free 0)
    , (3, Node Z 0 Free (Ptr 2 L) Free 0)
    ]

-- OP2-OP2
inBB :: Net
inBB = makeNet
  [ Node B 0 (Ptr 1 P) (Ptr 2 L) (Ptr 2 R) 0
  , Node B 0 (Ptr 0 P) (Ptr 3 L) (Ptr 3 R) 0
  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
  , Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0
  ]

outBB :: Net
outBB = Net nodes [0,1] [] where
  nodes = M.fromList $
    [ (2, Node Z 0 Free (Ptr 3 L) (Ptr 3 R) 0)
    , (3, Node Z 0 Free (Ptr 2 L) (Ptr 2 R) 0)
    ]

-- ITE-ITE
inII :: Net
inII = makeNet
  [ Node I 0 (Ptr 1 P) (Ptr 2 L) (Ptr 2 R) 0
  , Node I 0 (Ptr 0 P) (Ptr 3 L) (Ptr 3 R) 0
  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
  , Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0
  ]

outII :: Net
outII = Net nodes [0,1] [] where
  nodes = M.fromList $
    [ (2, Node Z 0 Free (Ptr 3 L) (Ptr 3 R) 0)
    , (3, Node Z 0 Free (Ptr 2 L) (Ptr 2 R) 0)
    ]

-- NUM-NUM
inNN :: Net
inNN = makeNet
  [ Node N 0 (Ptr 1 P) Free Free 2
  , Node N 0 (Ptr 0 P) Free Free 2
  ]

outNN :: Net
outNN = Net nodes [0,1] [] where
  nodes = M.empty

-- CON-ERA
inZE :: Net
inZE = makeNet
  [ Node Z 0 (Ptr 0 P) (Ptr 1 L) (Ptr 1 R) 0
  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
  ]

outZE :: Net
outZE = Net nodes [0] [] where
  nodes = M.fromList
    [(1, Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0)]

-- OP1-ERA
inUE :: Net
inUE = makeNet
  [ Node U 0 (Ptr 0 P) (Ptr 1 L) Free 1
  , Node Z 0 Free (Ptr 0 L) Free 0
  ]

outUE :: Net
outUE = Net nodes [0] [] where
  nodes = M.fromList
    [(1,Node Z 0 Free (Ptr 1 L) Free 0)]


-- OP2-ERA
inBE :: Net
inBE = makeNet
  [ Node B 0 (Ptr 0 P) (Ptr 1 L) (Ptr 1 R) 0
  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
  ]

outBE :: Net
outBE =  Net nodes [0] [] where
  nodes = M.fromList
    [(1,Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0)]

-- ITE-ERA
inIE :: Net
inIE = makeNet
  [ Node I 0 (Ptr 0 P) (Ptr 1 L) (Ptr 1 R) 0
  , Node Z 0 Free (Ptr 0 L) (Ptr 0 R) 0
  ]

outIE :: Net
outIE =  Net nodes [0] [] where
  nodes = M.fromList
    [(1,Node Z 0 Free (Ptr 1 L) (Ptr 1 R) 0)]

inNE :: Net
inNE = makeNet
  [ Node U 0 (Ptr 0 P) Free Free 1
  ]

outNE :: Net
outNE = Net nodes [0] [] where
  nodes = M.empty
