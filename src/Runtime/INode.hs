module Runtime.INode where

import           Data.Bits
import           Data.Word
import           Numeric     (showHex)
import           Text.Printf (PrintfArg, printf)

type Node = (Word64, Word64, Word64, Word64)

nodeInfo :: Node -> Word64
nodeInfo (i,p,l,r) = i

mainPort :: Node -> Word64
mainPort (i,m,l,r) = m

leftPort  :: Node -> Word64
leftPort (i,m,l,r) = l

rightPort :: Node -> Word64
rightPort (i,m,l,r) = r

showNode :: (Integer,Node) -> String
showNode (x,(i,m,l,r)) =
  case readInfoBits i of
  (Info True Con _ _ _ _ _ _)        -> show x ++ ":FREE_"
  (Info True Dup _ lS _ _ _ _)       -> show x ++ ":SET_" ++ showPort lS l
  (Info False n mS lS rS m1 m2 m3)   ->
    if (m1 == 0 && m2 == 0 && m3 == 0)
    then concat [show x, ":",show n, "_", showPort mS m, showPort lS l, showPort rS r]
    else concat [ show x, ":",show n, "_", showPort mS m, showPort lS l, showPort rS r
                , showHex m1 "", showHex m2 "", showHex m3 ""
                ]

showPort :: Slot -> Word64 -> String
showPort M n = "M" ++ showHex n ""
showPort L n = "L" ++ showHex n ""
showPort R n = "R" ++ showHex n ""

i64_truncate :: Word64 -> Word32
i64_truncate n = (fromIntegral n) .&. 0xFFFFFFFF

data Slot
  = M -- Main
  | L -- Left
  | R -- Right
  deriving (Enum, Show, Bounded, Eq, Ord)

data NType = Con | Dup deriving (Enum, Bounded, Eq, Show)

data Info = Info {
    isFree    :: Bool
  , ntype     :: NType
  , mainSlot  :: Slot
  , leftSlot  :: Slot
  , rightSlot :: Slot
  , meta1     :: Word8
  , meta2     :: Word16
  , meta3     :: Word32
  } deriving Eq

infoBits :: Info -> Word64
infoBits (Info f n mS lS rS m1 m2 m3)  = fromIntegral $
  (fromEnum f) +
  (fromEnum n)  `shiftL` 1 +
  (fromEnum mS) `shiftL` 2 +
  (fromEnum lS) `shiftL` 4 +
  (fromEnum rS) `shiftL` 6 +
  (fromEnum m1) `shiftL` 8 +
  (fromEnum m2) `shiftL` 16 +
  (fromEnum m3) `shiftL` 32

readInfoBits :: Word64 -> Info
readInfoBits x = let n = (fromIntegral x) in Info
  (toEnum $ n               .&. 0x1)
  (toEnum $ (n `shiftR` 1)  .&. 0x1)
  (toEnum $ (n `shiftR` 2)  .&. 0x3)
  (toEnum $ (n `shiftR` 4)  .&. 0x3)
  (toEnum $ (n `shiftR` 6)  .&. 0x3)
  (toEnum $ (n `shiftR` 8)  .&. 0xFF)
  (toEnum $ (n `shiftR` 16) .&. 0xFFFF)
  (toEnum $ (n `shiftR` 32) .&. 0xFFFFFFFF)

instance Enum Info where
  toEnum = readInfoBits . fromIntegral
  fromEnum = fromIntegral . infoBits

instance Show Info where
  show (Info f n m l r m1 m2 m3)
    | f = "F"
    | m1 == 0 && m2 == 0 && m3 == 0 = concat [show n, ":", show m, show l, show r]
    | otherwise = concat
      [ show n, ":" , show m, show l, show r
      , showHex m1 "", showHex m2 "", showHex m3 ""
      ]

printBits :: (PrintfArg a) => a -> IO ()
printBits n = do
  putStrLn $ printf "%08b" n

mkNode :: NType -> Slot -> Word64 -> Slot -> Word64 -> Slot -> Word64 -> Node
mkNode n mS m lS l rS r = ((infoBits (Info False n mS lS rS 0 0 0)),m,l,r)

mkFree :: Word64 -> Node
mkFree i = ((infoBits (Info True Con M L R 0 0 0)),i,i,i)

mkSet  :: Slot -> Word64 -> Node
mkSet s n = ((infoBits (Info True Dup L s L 0 0 0)),0,n,0)

getNType :: Node -> NType
getNType (i,_,_,_) = ntype $ readInfoBits i

