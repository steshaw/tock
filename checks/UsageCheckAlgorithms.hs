{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

module UsageCheckAlgorithms (checkPar, findReachDef, joinCheckParFunctions) where

import Data.Graph.Inductive
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import FlowAlgorithms
import FlowGraph
import Metadata
import UsageCheckUtils
import Utils

joinCheckParFunctions :: Monad m => ((Meta, ParItems a) -> m b) -> ((Meta, ParItems a) -> m c) -> ((Meta, ParItems a) -> m (b,c))
joinCheckParFunctions f g x = seqPair (f x, g x)

-- | Given a function to check a list of graph labels and a flow graph,
-- returns a list of monadic actions (slightly
-- more flexible than a monadic action giving a list) that will check
-- all PAR items in the flow graph
checkPar :: forall m a b. Monad m => ((Meta, ParItems a) -> m b) -> FlowGraph m a -> [m b]
checkPar f g = map f allParItems
  where
    -- TODO deal with replicators
  
    allStartParEdges :: Map.Map Int [(Node,Node)]
    allStartParEdges = foldl (\mp (s,e,n) -> Map.insertWith (++) n [(s,e)] mp) Map.empty $ mapMaybe tagStartParEdge $ labEdges g
  
    tagStartParEdge :: (Node,Node,EdgeLabel) -> Maybe (Node,Node,Int)
    tagStartParEdge (s,e,EStartPar n) = Just (s,e,n)
    tagStartParEdge _ = Nothing
    
    allParItems :: [(Meta, ParItems a)]
    allParItems = map makeEntry $ map findNodes $ Map.toList allStartParEdges
      where
        findNodes :: (Int,[(Node,Node)]) -> (Node,[ParItems a])
        findNodes (n,ses) = (undefined, [SeqItems (followUntilEdge e (EEndPar n)) | (_,e) <- ses])
        
        makeEntry :: (Node,[ParItems a]) -> (Meta, ParItems a)
        makeEntry (_,xs) = (emptyMeta {- TODO fix this again -} , ParItems xs)
    
    -- | We need to follow all edges out of a particular node until we reach
    -- an edge that matches the given edge.  So what we effectively need
    -- is a depth-first or breadth-first search (DFS or BFS), that terminates
    -- on a given edge, not on a given node.  Therefore the DFS/BFS algorithms
    -- that come with the inductive graph package are not very suitable as
    -- they return node lists or edge lists, but we need a node list terminated
    -- on a particular edge.
    --
    -- So, we shall attempt our own algorithm!  The algorithm for DFS given in 
    -- the library is effectively:
    --
    -- dfs :: Graph gr => [Node] -> gr a b -> [Node]
    -- dfs [] _ = []
    -- dfs _ g | isEmpty g = []
    -- dfs (v:vs) g = case match v g of
    --                  (Just c,g')  -> node' c:dfs (suc' c++vs) g'
    --                  (Nothing,g') -> dfs vs g'
    -- where node' :: Context a b -> Node and suc' :: Context a b -> [Node]
    --
    -- We want to stop the DFS branch either when we find no nodes following the current
    -- one (already effectively taken care of in the algorithm above; suc' will return
    -- the empty list) or when the edge we are meant to take matches the given edge.
    followUntilEdge :: Node -> EdgeLabel -> [a]
    followUntilEdge startNode endEdge = customDFS [startNode] g
      where
        customDFS :: [Node] -> FlowGraph m a -> [a]
        customDFS [] _ = []
        customDFS _ g | isEmpty g = []
        customDFS (v:vs) g = case match v g of
                               (Just c, g') -> labelItem c : customDFS (customSucc c ++ vs) g'
                               (Nothing, g') -> customDFS vs g'
        
        labelItem :: Context (FNode m a) EdgeLabel -> a
        labelItem c = let (Node (_,x,_)) = lab' c in x
        
        customSucc :: Context (FNode m a) EdgeLabel -> [Node]
        customSucc c = [n | (n,e) <- lsuc' c, e /= endEdge]

-- | Returns either an error, or map *from* the node with a read, *to* the node whose definitions might be available at that point
findReachDef :: forall m. Monad m => FlowGraph m (Maybe Decl, Vars) -> Node -> Either String (Map.Map Node (Map.Map Var (Set.Set Node)))
findReachDef graph startNode
  = do r <- flowAlgorithm graphFuncs (nodes graph) startNode
       -- These lines remove the maps where the variable is not read in that particular node:
       let r' = Map.mapWithKey (\n -> Map.filterWithKey (readInNode' n)) r
       return $ Map.filter (not . Map.null) r'
  where
    graphFuncs :: GraphFuncs Node EdgeLabel (Map.Map Var (Set.Set Node))
    graphFuncs = GF
      {
        nodeFunc = processNode
        ,prevNodes = lpre graph
        ,nextNodes = lsuc graph
        ,initVal = Map.empty
        ,defVal = Map.empty
      }

    readInNode' :: Node -> Var -> a -> Bool
    readInNode' n v _ = readInNode v (lab graph n)

    readInNode :: Var -> Maybe (FNode m (Maybe Decl, Vars)) -> Bool
    readInNode v (Just (Node (_,(_,Vars read _ _),_))) = Set.member v read
    
    writeNode :: FNode m (Maybe Decl, Vars) -> Set.Set Var
    writeNode (Node (_,(_,Vars _ written _),_)) = written
      
    -- | A confusiing function used by processNode.   It takes a node and node label, and uses
    -- these to form a multi-map modifier function that replaces all node-sources for variables
    -- written to by the given with node with a singleton set containing the given node.
    -- That is, nodeLabelToMapInsert N (Node (_,Vars _ written _ _)) is a function that replaces
    -- the sets for each v (v in written) with a singleton set {N}.
    nodeLabelToMapInsert :: Node -> FNode m (Maybe Decl, Vars) -> Map.Map Var (Set.Set Node) -> Map.Map Var (Set.Set Node)
    nodeLabelToMapInsert n = foldFuncs . (map (\v -> Map.insert v (Set.singleton n) )) . Set.toList . writeNode
      
    processNode :: (Node, EdgeLabel) -> Map.Map Var (Set.Set Node) -> Maybe (Map.Map Var (Set.Set Node)) -> Map.Map Var (Set.Set Node)
    processNode (n,_) inputVal mm = mergeMultiMaps modifiedInput prevAgg
      where
        prevAgg :: Map.Map Var (Set.Set Node)
        prevAgg = fromMaybe Map.empty mm
        
        modifiedInput :: Map.Map Var (Set.Set Node)
        modifiedInput = (maybe id (nodeLabelToMapInsert n) $ lab graph n) inputVal
    
    -- | Merges two "multi-maps" (maps to sets) using union
    mergeMultiMaps :: (Ord k, Ord a) => Map.Map k (Set.Set a) -> Map.Map k (Set.Set a) -> Map.Map k (Set.Set a)
    mergeMultiMaps = Map.unionWith (Set.union)
