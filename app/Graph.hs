module Graph where

import           Data.List
import           Data.Word
import           System.IO
import           System.Process

import           Runtime.INet
import           Runtime.INode

import           Data.Set            (Set)
import qualified Data.Set            as Set
import qualified Data.Vector.Unboxed as V

graph :: FilePath -> String -> Net -> IO ()
graph file str net = do
  writeFile file (graphVizNet net)
  runCommand $ "dot -Tsvg " ++ show file ++ "> " ++ str ++ ".svg"
  return ()

graphVizNet :: Net -> String
graphVizNet n = intercalate "\n" $
  [ "graph structs {"
  , "  node [shape=none, fontsize=10,fontname=\"Courier\"]"
  , concatMap nodeString (zip [0..] (V.toList $ nodes n))
  , concatMap (edgeString (redex n)) (edges $ nodes n)
  , "}"
  ]

nodeString :: (Integer, Node) -> String
nodeString (i, (b,_,_,_)) = case readInfoBits b of
  (Info True Con _ _ _ _ _ _)        -> intercalate "\n"
    [ "\n  n" ++ show i ++ " [label=<"
    , "  <table bgcolor=\"orangered\" border=\"1\" cellborder=\"0\" cellspacing=\"0\">"
    , "  <tr><td colspan=\"2\" port=\"L\" bgcolor=\"orangered\">" ++ show i ++ "</td></tr>"
    , "  </table>>];"
    ]
  (Info True Dup _ _ _ _ _ _)       -> intercalate "\n"
    [ "\n  n" ++ show i ++ " [label=<"
    , "  <table bgcolor=\"lightgrey\" border=\"0\" cellborder=\"1\" cellspacing=\"2\">"
    , "  <tr><td colspan=\"2\" port=\"L\" bgcolor=\"beige\">" ++ show i ++ "</td></tr>"
    , "  </table>>];"
    ]
  (Info False Con _ _ _ _ _ _)   -> intercalate "\n"
    [ "\n  n" ++ show i ++ " [label=<"
    , "  <table bgcolor=\"lightgrey\" border=\"0\" cellborder=\"1\" cellspacing=\"2\">"
    , "  <tr><td colspan=\"2\" port=\"M\" bgcolor=\"lightblue\">" ++ show i ++ "</td></tr>"
    , "  <tr><td port=\"L\">L</td><td port=\"R\">R</td></tr>"
    , "  </table>>];"
    ]
  (Info False Dup _ _ _ _ _ _)   -> intercalate "\n"
    [ "\n  n" ++ show i ++ " [label=<"
    , "  <table bgcolor=\"lightgrey\" border=\"0\" cellborder=\"1\" cellspacing=\"2\">"
    , "  <tr><td colspan=\"2\" port=\"M\" bgcolor=\"palegreen\">" ++ show i ++ "</td></tr>"
    , "  <tr><td port=\"L\">L</td><td port=\"R\">R</td></tr>"
    , "  </table>>];"
    ]

edgeString :: [(Word64, Word64)] -> Edge -> String
edgeString rs (Edge sA iA sB iB)
  | (iA,iB) `elem` rs || (iB, iA) `elem` rs =
    concat ["  n",show iA,":",show sA,"--","n",show iB,":",show sB, "[color=red]\n"]
  | otherwise =
    concat ["  n",show iA,":",show sA,"--","n",show iB,":",show sB,"[color=black]\n"]

data Edge = Edge Slot Word64 Slot Word64 deriving (Eq,Show, Ord)

edges :: V.Vector Node -> [Edge]
edges vs = Set.toList $ V.ifoldr insertRedex Set.empty vs
  where
    insertRedex :: Int -> Node -> Set Edge -> Set Edge
    insertRedex i (b,m,l,r) set = case (f,t) of
      (True, Con) -> set
      (True, Dup) -> insert' (Edge L i' lS l) $ set
      (False, _) ->
        insert' (Edge M i' mS m) $
        insert' (Edge L i' lS l) $
        insert' (Edge R i' rS r) $ set
      where
       (Info f t mS lS rS _ _ _) = readInfoBits b
       i' = fromIntegral i
       insert' n@(Edge sA iA sB iB) s
         | Set.member (Edge sB iB sA iA) set = s
         | otherwise = Set.insert n s


