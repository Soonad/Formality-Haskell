{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
module FormalityNet where

import           Control.Monad                  (guard, unless, when)
import           Control.Monad.Trans.State.Lazy
import qualified Data.Map.Strict                as M
import qualified Data.Set                       as Set

data Net = Net
  { netNodes   :: M.Map Int Node
  , freedNodes :: [Int]
  , netRedex   :: [(Int, Int)]
  } deriving (Eq, Show)

data Port
  = Ptr { toNode :: Int, toSlot :: Slot }
  | Free
  deriving Eq

instance Show Port where
  show Free      = "F"
  show (Ptr n s) = show n ++ show s

data Slot = P | L | R deriving (Eq, Show)
type Kind = Int

-- With the Eraser node, the mnemonic is "EZUBIN"
data NodeType
  = Z -- Constructor
  | U -- Unary Arithmetic Operator
  | B -- Binary Arithmetic Operator
  | I -- Iterator
  | N -- Number
  deriving (Eq, Show)

data Node = Node
  { typeOf :: NodeType
  , kind   :: Kind
  , slotP  :: Port
  , slotL  :: Port
  , slotR  :: Port
  , num    :: Int
  } deriving Eq

instance Show Node where
  show (Node Z k sP sL sR n) =
    concat ["Z",show k,"{",show sP,",",show sL,",",show sR,"}"]
  show (Node U k sP sL sR n) =
    concat ["U",show k,show n,"{",show sP,",",show sL,"}"]
  show (Node B k sP sL sR n) =
    concat ["B",show k,"{",show sP,",",show sL,",",show sR,"}"]
  show (Node I k sP sL sR n) =
    concat ["I",show k,"{",show sP,",",show sL,",",show sR,"}"]
  show (Node N k sP sL sR n) =
    concat ["N",show n,"{",show sP,"}"]

defaultNode :: Int -> NodeType -> Kind -> Int -> Node
defaultNode i nt k num = Node nt k (Ptr i P) (Ptr i L) (Ptr i R) num

makeNet :: [Node] -> Net
makeNet nodes = let n = M.fromList $ zip [0..] nodes in Net n [] (findRedexes n)

findRedexes :: M.Map Int Node -> [(Int, Int)]
findRedexes nodes = deDup $ (toNode . slotP) <$> M.filterWithKey isRedex nodes
  where
    isRedex _ n = case slotP n of
      (Ptr _ P) -> True
      _         -> False
    deDup = Set.toList . (M.foldrWithKey f Set.empty)
    f k v s
      | Set.member (v, k) s = s
      | otherwise = (Set.insert (k, v) s)

slot :: Slot -> Node -> Port
slot s n = case s of P -> slotP n; L -> slotL n; R -> slotR n

setSlot :: Slot -> Port -> Node -> Node
setSlot s q n = case s of
  P -> n { slotP = q }; L -> n {slotL = q }; R -> n { slotR = q }

allocNode :: NodeType -> Kind -> Int -> State Net Int
allocNode t k n = do
  freed <- gets freedNodes
  case freed of
    (f:_) -> return f
    [] -> do
      addr <- gets $ (maybe 0 ((+1) . fst)) . M.lookupMax . netNodes
      let node = defaultNode addr t k n
      modify (\n -> n { netNodes = M.insert addr node $ netNodes n })
      return addr

freeNode :: Int -> State Net ()
freeNode addr = do
  modify $ \n -> n
      { netNodes = M.delete addr $ netNodes n
      , freedNodes = addr : (freedNodes n)
      }

getPort :: Int -> Slot -> M.Map Int Node -> Port
getPort addr s net = (slot s) (net M.! addr)

setPort :: Int -> Slot -> Port -> State Net ()
setPort addr s port = modify $ \net ->
  net {netNodes = M.adjust (setSlot s port) addr $ netNodes net }

linkSlots :: (Int, Slot) -> (Int, Slot) -> State Net ()
linkSlots (ia, sa) (ib, sb) = do
  setPort ia sa $ Ptr ib sb
  setPort ib sb $ Ptr ia sa
  when (sa == P && sb == P) $
    modify (\n -> n {netRedex = (ia,ib) : netRedex n})

linkPorts :: (Int, Slot) -> (Int, Slot) -> State Net ()
linkPorts (ia, sa) (ib, sb) = do
  net <- gets netNodes
  case (getPort ia sa net, getPort ib sb net) of
    (Ptr ia' sa', Ptr ib' sb') -> linkSlots (ia', sa') (ib', sb')
    (Ptr ia' sa', x)           -> setPort ia' sa' x
    (x, Ptr ib' sb')           -> setPort ib' sb' x
    _                          -> return ()

unlinkPort :: (Int, Slot) -> State Net ()
unlinkPort (ia, sa) = do
  net <- gets netNodes
  case (getPort ia sa net) of
    (Ptr ib sb) -> do
      setPort ia sa $ Ptr ia sa
      setPort ib sb $ Ptr ib sb
    _ -> return ()

rewrite :: (Int, Int) -> State Net ()
rewrite (iA, iB) = do

  match iA iB

  freeNode iA
  unless (iA == iB) (freeNode iB)

match :: Int -> Int -> State Net ()
match iA iB = do
  net <- gets netNodes
  let a = net M.! iA
  let b = net M.! iB

  case (typeOf a, typeOf b) of
    (Z, Z) -> if
      | kind a == kind b -> annihilate iA iB
      | otherwise        -> duplicate (iA, a) (iB, b)
    (U, U) -> linkPorts (iA, L) (iB, L)
    (B, B) -> annihilate iA iB
    (I, I) -> annihilate iA iB
    (N, N) -> pure ()

    (Z, B) -> duplicate (iA, a) (iB, b)
    (Z, I) -> duplicate (iA, a) (iB, b)
    (Z, N) -> do
      iP <- allocNode N 0 (num b)
      iQ <- allocNode N 0 (num b)
      linkPorts (iA, L) (iP, P)
      linkPorts (iA, R) (iQ, P)

    (U, Z) -> duplicate1 (iA, a) (iB, b)
    (U, B) -> duplicate1 (iA, a) (iB, b)
    (U, I) -> duplicate1 (iA, a) (iB, b)
    (U, N) -> do
      let x = arithmetic (kind a) (num b) (num a)
      iP <- allocNode N 0 (num b)
      linkPorts (iA, L) (iP, P)

    (B, I) -> duplicate (iA, a) (iB, b)
    (B, N) -> do
      iP <- allocNode U (kind a) (num b)
      linkPorts (iA, L) (iP, P)
      linkPorts (iA, R) (iP, L)

    (I, N) -> do
      iP <- allocNode Z (kind a) 0
      linkPorts (iA, L) (iP, P)
      if
        | (num b) == 0 -> linkPorts (iA, R) (iP,L)
        | otherwise    -> linkPorts (iA, R) (iP,R)

    _ -> match iB iA

annihilate :: Int -> Int -> State Net ()
annihilate iA iB = do
  linkPorts (iA, L) (iB, L)
  linkPorts (iA, R) (iB, R)

duplicate1 :: (Int, Node) -> (Int, Node) -> State Net ()
duplicate1 (iA, a) (iB, b) = do
  iP <- allocNode (typeOf b) (kind b) 0
  iQ <- allocNode (typeOf b) (kind b) 0
  iR <- allocNode (typeOf a) (kind a) 0
  linkSlots (iR, R) (iQ, L)
  linkSlots (iR, L) (iP, L)
  linkPorts (iP,P) (iA,L)
  linkPorts (iQ,P) (iA,R)
  linkPorts (iR,P) (iB,L)

duplicate :: (Int, Node) -> (Int, Node) -> State Net ()
duplicate (iA, a) (iB, b) = do
  iP <- allocNode (typeOf b) (kind b) 0
  iQ <- allocNode (typeOf b) (kind b) 0
  iR <- allocNode (typeOf a) (kind a) 0
  iS <- allocNode (typeOf a) (kind a) 0
  linkSlots (iS, L) (iP, R)
  linkSlots (iR, R) (iQ, L)
  linkSlots (iS, R) (iQ, R)
  linkSlots (iR, L) (iP, L)
  linkPorts (iP,P) (iA,L)
  linkPorts (iQ,P) (iA,R)
  linkPorts (iR,P) (iB,L)
  linkPorts (iS,P) (iB,R)

arithmetic :: Kind -> Int -> Int -> Int
arithmetic f n m =
  case f of
    0 -> n + m
    1 -> n - m
    2 -> n * m
    3 -> n `div` m
    4 -> n `mod` m
    5 -> n ^ m
    6 -> n ^ (m `div` (2 ^ 32))
--    7 -> n `and` m
--    8 -> n `or` m
--    9 -> n `xor` m
--    10 -> not m
--    11 -> lsh n m
--    12 -> rsh n m
--    13 -> if n > m then 1 else 0
--    14 -> if n < m then 1 else 0
--    15 -> if n == m then 1 else 0
    _ -> error "[ERROR]\nInvalid interaction"

reduce :: Net -> (Net, Int)
reduce net =
  let go net count =
        case netRedex net of
          [] -> (net, count)
          r:rs -> let newNet = execState (rewrite r) (net { netRedex = rs })
                   in go newNet (count + 1)
  in go net 0



