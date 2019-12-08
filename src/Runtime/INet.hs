{-# LANGUAGE MultiWayIf #-}
module Runtime.INet where


import           Control.Monad.State.Strict
import           Data.List                  (intercalate)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import qualified Data.Vector.Unboxed        as V
import           Data.Word

import           Runtime.INode

data Net =
  Net { nodes :: V.Vector Node
      , freed :: [Word64]
      , redex :: [(Word64,Word64)]
      } deriving (Eq)

instance Show Net where
  show (Net ws fs rs) = concat $
      [ intercalate "\n" (showNode <$> (zip [0..] (V.toList ws)))
      , "\n"
      , "FREE:", show fs
      , "\n"
      , "REDEX:", show rs
      ]

testNodes :: [Node]
testNodes =
  [ mkNode Con M 0 L 1 L 0
  -- , Node (labelBits (Label True Con M R R)) 0 1 1
  , mkNode Con M 0 R 1 R 1
  ]

testWords :: V.Vector Node
testWords = V.fromList testNodes

findRedexes :: V.Vector Node -> [(Word64, Word64)]
findRedexes vs = Set.toList $ V.ifoldr insertRedex Set.empty vs
  where
    insertRedex :: Int -> Node -> Set (Word64, Word64) -> Set (Word64, Word64)
    insertRedex i (b,m,l,r) set
      |    mainSlot (readInfoBits b) == M
        && mainSlot (readInfoBits b') == M
        && i == fromIntegral m'
        && not (Set.member (m,m') set)
        = Set.insert (m',m) set
      | otherwise = set
        where
         (b',m',l',r')  = vs V.! (fromIntegral m)

makeNet :: [Node] -> Net
makeNet nodes = let vs = V.fromList nodes in Net vs [] (findRedexes vs)

testNet :: Net
testNet = makeNet testNodes

allocNode :: NType -> State Net Word64
allocNode n = do
  (Net vs fs rs) <- get
  let node i = (infoBits (Info False n M L R 0 0 0), i, i, i)
  case fs of
    [] -> do
      let i = fromIntegral (V.length vs)
      modify (\n -> n { nodes = vs `V.snoc` (node i)})
      return i
    (f:fs) -> do
      modify (\n -> n { nodes = vs V.// [(fromIntegral f,node f)], freed = fs})
      return f

--isFreed :: Word64 -> State Net Bool
--isFreed i = do
--  n <- (\x -> x V.! (fromIntegral i)) <$> gets nodes
--  return $ getNType n == Fre

freeNode :: Word64 -> State Net ()
freeNode i = modify (\n ->
    n { nodes = (nodes n) V.// [(fromIntegral i,(1,i,i,i))]
      , freed = i:(freed n)
      })

getNode :: Word64 -> State Net Node
getNode i = (\vs -> vs V.! (fromIntegral i)) <$> gets nodes

getPort :: Slot -> Node -> (Slot, Word64)
getPort s (b,m,l,r) =
  let i = readInfoBits b in
  case s of
    M ->  (mainSlot  i,m)
    L ->  (leftSlot  i,l)
    R ->  (rightSlot i,r)

enterPort :: (Slot, Word64) -> State Net (Slot,Word64)
enterPort (s, n) = do
  node <- getNode n
  return $ (getPort s node)

setSlot :: Node -> Slot -> (Slot, Word64) -> Node
setSlot node@(b,m,l,r) x (s,n)  =
  let i = readInfoBits b in
  case x of
  M -> (infoBits $ i { mainSlot = s }, n, l, r)
  L -> (infoBits $ i { leftSlot = s    }, m, n, r)
  R -> (infoBits $ i { rightSlot = s   }, m, l, n)

setPort :: Slot -> Word64 -> (Slot,Word64) -> State Net ()
setPort s i port = do
  node <- ((\x -> x V.! (fromIntegral i)) <$> gets nodes)
  modify $ \n ->
    n { nodes = (nodes n) V.// [(fromIntegral i, (setSlot node s port))] }

linkSlots :: (Slot,Word64) -> (Slot, Word64) -> State Net ()
linkSlots (sa,ia) (sb,ib) = do
  setPort sa ia $ (sb,ib)
  setPort sb ib $ (sa,ia)
  when (sa == M && sb == M) $
   modify (\n -> n { redex = (ia, ib) : redex n })

linkPorts :: (Slot,Word64) -> (Slot,Word64) -> State Net ()
linkPorts (sa,ia) (sb,ib) = linkSlots (sa,ia) (sb,ib)

unlinkPort :: (Slot,Word64) -> State Net ()
unlinkPort (sa,ia) = do
  (sb,ib) <- enterPort (sa,ia)
  (sa',ia') <- enterPort (sb,ib)
  if (ia' == ia && sa' == sa) then do
      setPort sa ia (sa,ia)
      setPort sb ib (sb,ib)
    else return ()

rewrite :: (Word64, Word64) -> State Net ()
rewrite (iA, iB) = do
  nodes <- gets $ nodes
  let a = nodes V.! (fromIntegral iA)
  let b = nodes V.! (fromIntegral iB)
  if
    | (getNType a == getNType b) -> do
      aLdest <- enterPort (L,iA)
      bLdest <- enterPort (L,iB)
      linkPorts aLdest bLdest
      aRdest <- enterPort (R,iA)
      bRdest <- enterPort (R,iB)
      linkPorts aRdest bRdest
      return ()
    | otherwise -> do
      iP <- allocNode (getNType b)
      iQ <- allocNode (getNType b)
      iR <- allocNode (getNType a)
      iS <- allocNode (getNType a)
      linkSlots (L,iS) (R,iP)
      linkSlots (R,iR) (L,iQ)
      linkSlots (R,iS) (R,iQ)
      linkSlots (L,iR) (L,iP)
      a1dest <- enterPort (L,iA)
      a2dest <- enterPort (R,iA)
      b1dest <- enterPort (L,iB)
      b2dest <- enterPort (R,iB)
      linkPorts (M,iP) a1dest
      linkPorts (M,iQ) a2dest
      linkPorts (M,iR) b1dest
      linkPorts (M,iS) b2dest
  mapM_ (\x -> unlinkPort (x,iA)) [M,L,R] >> freeNode iA
  unless (iA == iB) (mapM_ (\x -> unlinkPort (x,iB)) [M,L,R] >> freeNode iB)
  return ()

reduce :: Net -> (Net, Int)
reduce x = go (x {redex = (findRedexes (nodes x))}) 0
  where
    go n c = case redex n of
      []   -> (n, c)
      r:rs -> go (execState (rewrite r) (n { redex = rs })) (c + 1)

inCD :: Net
inCD= makeNet
  [ mkNode Con M 1 L 2 L 3
  , mkNode Dup M 0 L 4 L 5
  , mkSet L 0
  , mkSet R 0
  , mkSet L 1
  , mkSet R 1
  ]

inCC :: Net
inCC = makeNet
  [ mkNode Con M 1 L 2 L 3
  , mkNode Con M 0 L 4 L 5
  , mkSet L 0
  , mkSet R 0
  , mkSet L 1
  , mkSet R 1
  ]

inCE :: Net
inCE = makeNet
  [ mkNode Con M 0 L 1 L 2
  , mkSet L 0
  , mkSet R 0
  ]
