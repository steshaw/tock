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

import Control.Monad.State

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
makeMeta n = Meta (Just "FlowGraphTest") n 0

-- To make typing the tests as short as possible:
m0 = makeMeta 0
m1 = makeMeta 1
m2 = makeMeta 2
m3 = makeMeta 3
m4 = makeMeta 4
m5 = makeMeta 5
m6 = makeMeta 6
m7 = makeMeta 7

sub :: Meta -> Int -> Meta
sub m n = m {metaColumn = n}

sm0 = A.Skip m0
sm1 = A.Skip m1
sm2 = A.Skip m2
sm3 = A.Skip m3
sm4 = A.Skip m4
sm5 = A.Skip m5
sm6 = A.Skip m6
sm7 = A.Skip m7

showGraph :: (Graph g, Show a, Show b) => g a b -> String
showGraph g = " Nodes: " ++ show (labNodes g) ++ " Edges: " ++ show (labEdges g)

nextId :: Data t => t -> State (Map.Map Meta Int) Int
nextId t = do mp <- get
              case Map.lookup m mp of
                Just n -> do put $ Map.adjust ((+) 1) m mp
                             return n
                Nothing -> do put $ Map.insert m 1 mp
                              return 0
              where m = findMeta t

testGraph :: String -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Process -> Test
testGraph testName nodes edges proc
  = TestCase $ 
      case evalState (buildFlowGraph nextId nextId (A.OnlyP emptyMeta proc)) Map.empty of
        Left err -> assertFailure (testName ++ " graph building failed: " ++ err)
        Right g -> checkGraphEquality (nodes, edges) g
  where  
    -- Checks two graphs are equal by creating a node mapping from the expected graph to the real map (checkNodeEquality),
    -- then mapping the edges across (transformEdge) and checking everything is right (in checkGraphEquality)
    
    checkGraphEquality :: (Graph g, Show b, Ord b) => ([(Int, Meta)], [(Int, Int, b)]) -> g (Meta, Int) b -> Assertion
    checkGraphEquality (nodes, edges) g
      = do let (remainingNodes, nodeLookup, ass) = foldl checkNodeEquality (Map.fromList (map revPair nodes),Map.empty, return ()) (labNodes g)
           ass
           assertBool (testName ++ " Test graph had nodes not found in the real graph: " ++ show remainingNodes ++ ", real graph: " ++ showGraph g) (Map.null remainingNodes)
           edges' <- mapM (transformEdge nodeLookup) edges
           assertEqual (testName ++ " Edge lists not equal") (sort $ edges') (sort $ labEdges g)
    
    checkNodeEquality :: (Map.Map Meta Int, Map.Map Int Int, Assertion) -> (Node, (Meta, Int)) -> (Map.Map Meta Int, Map.Map Int Int, Assertion)
    checkNodeEquality (metaToTestId, realToTestId, ass) (nodeId, (metaTag,metaSub))
      = case Map.lookup (sub metaTag metaSub) metaToTestId of
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
