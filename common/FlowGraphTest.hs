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

module FlowGraphTest (tests) where

import Data.Generics
import Data.Graph.Inductive
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Test.HUnit hiding (Node, State)

import qualified AST as A
import FlowGraph
import Metadata
import Utils

makeMeta :: Int -> Meta
makeMeta n = Meta (Just "FlowGraphTest") n n

-- To make typing the tests as short as possible:
m0 = makeMeta 0
m1 = makeMeta 1
m2 = makeMeta 2
m3 = makeMeta 3
m4 = makeMeta 4

sm0 = A.Skip m0
sm1 = A.Skip m1
sm2 = A.Skip m2
sm3 = A.Skip m3
sm4 = A.Skip m4

showGraph :: Graph g => g a b -> String
showGraph g = " Nodes: " ++ show (nodes g) ++ " Edges: " ++ show (edges g)

testGraph :: String -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Process -> Test
testGraph testName nodes edges proc
  = TestCase $ 
      case buildFlowGraph () (const ()) (A.OnlyP emptyMeta proc) of
        Left err -> assertFailure (testName ++ " graph building failed: " ++ err)
        Right g -> checkGraphEquality (nodes, edges) g
  where
    checkGraphEquality :: (Graph g, Show b, Ord b) => ([(Int, Meta)], [(Int, Int, b)]) -> g (Meta, a) b -> Assertion
--    checkGraphEquality ([],[]) g = assertBool (testName ++ " Graph had nodes or edges remaining: " ++ showGraph g) (isEmpty g)
    checkGraphEquality (nodes, edges) g
      = do let (remainingNodes, nodeLookup, ass) = ufold checkNodeEquality (Map.fromList (map revPair nodes),Map.empty, return ()) g
           ass
           assertBool (testName ++ " Test graph had nodes not found in the real graph: " ++ show remainingNodes) (Map.null remainingNodes)
           edges' <- mapM (transformEdge nodeLookup) edges
           let (remainingEdges, ass') = ufold checkEdgeEquality (makeEdgeMap edges',return ()) g
           ass'
           assertBool (testName ++ " Test graph had edges not found in the real graph: " ++ show remainingEdges) (Map.null remainingEdges)
    
    checkNodeEquality :: Show b => Context (Meta, a) b -> (Map.Map Meta Int, Map.Map Int Int, Assertion) -> (Map.Map Meta Int, Map.Map Int Int, Assertion)
    checkNodeEquality (_linksTo, nodeId, (metaTag,_), _linksFrom) (metaToTestId, realToTestId, ass)
      = case Map.lookup metaTag metaToTestId of
          Nothing -> (metaToTestId, realToTestId, ass >> assertFailure ("Node with meta tag " ++ show metaTag ++ " not found in expected test data"))
          Just testId -> let realToTestId' = Map.insert nodeId testId realToTestId in
                         let metaToTestId' = Map.delete metaTag metaToTestId in
                         (metaToTestId', realToTestId', ass)
    transformEdge :: Show b => Map.Map Int Int -> (Int, Int, b) -> IO (Int, Int, b)
    transformEdge nodeMap e@(start, end, label)
      = case mergeMaybe (Map.lookup start nodeMap) (Map.lookup end nodeMap) of
          Nothing -> do assertFailure ("Could not map test edge to real edge: " ++ show e)
                        return e
          Just (start', end') -> return (start', end', label)
    
    checkEdgeEquality :: (Show b, Ord b) => Context (Meta, a) b -> (Map.Map Int [(Int, Int, b)], Assertion) -> (Map.Map Int [(Int, Int, b)], Assertion) 
    checkEdgeEquality (linksTo, nodeId, _metaTagPair, linksFrom) (nodeToEdges, ass)
      = (
          Map.delete nodeId nodeToEdges
          ,ass >> (assertEqual (testName ++ " Edge lists not equal")
            ((sort . concat . maybeToList) $ Map.lookup nodeId nodeToEdges)
            (sort $ (map (addSrc nodeId) linksFrom) ++ (map (addDest nodeId) linksTo)))
         )
           
    addSrc :: Int -> (b, Node) -> (Int, Int, b)
    addSrc src (x, dest) = (src, dest, x)
    
    addDest :: Int -> (b, Node) -> (Int, Int, b)
    addDest dest (x, src) = (src, dest, x)
    
    makeEdgeMap :: [(Int, Int, b)] -> Map.Map Int [(Int, Int, b)]
    makeEdgeMap = foldl makeEdgeMap' Map.empty
      where
        makeEdgeMap' :: Map.Map Int [(Int, Int, b)] -> (Int,Int,b) -> Map.Map Int [(Int, Int, b)]
        makeEdgeMap' mp edge@(start, end, label) = Map.insertWith (++) start [edge] (Map.insertWith (++) end [edge] mp)

testSeq :: Test
testSeq = TestList
 [
   testSeq' 0 [(0,m1)] [] (A.Several m1 [])
  ,testSeq' 1 [(0,m2)] [] (A.OnlyP m1 sm2)
  --TODO need some sort of primary key for nodes?
  --,testSeq' 2 [(0,m1), (1,m2)] [(0,1,ESeq),(1,
 ]
  where
    testSeq' :: Int -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Structured -> Test
    testSeq' n a b s = testGraph ("testSeq " ++ show n) a b (A.Seq m0 s)

--Returns the list of tests:
tests :: Test
tests = TestList
 [
  testSeq
 ]
