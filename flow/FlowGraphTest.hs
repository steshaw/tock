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

-- #ignore-exports

-- | A module for testing building a control flow-graph from an AST.
module FlowGraphTest (qcTests) where

import Control.Monad.Identity
import Control.Monad.State

import Data.Generics
import Data.Graph.Inductive
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import System.Random
import Test.HUnit hiding (Node, State, Testable)
import Test.QuickCheck

import qualified AST as A
import FlowGraph
import Metadata
import PrettyShow
import TestFramework
import TestUtils
import Utils

-- | Makes a distinctive metatag for testing.  The function is one-to-one.
makeMeta :: Int -> Meta
makeMeta n = Meta (Just "FlowGraphTest") n 0

m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, mU :: Meta
-- To make typing the tests as short as possible (typing a function call means bracketing is needed, which is a pain):
m0 = makeMeta 0
m1 = makeMeta 1
m2 = makeMeta 2
m3 = makeMeta 3
m4 = makeMeta 4
m5 = makeMeta 5
m6 = makeMeta 6
m7 = makeMeta 7
m8 = makeMeta 8
m9 = makeMeta 9
m10 = makeMeta 10
m11 = makeMeta 11
-- | For meta tags that shouldn't be used in the graph:
mU = makeMeta (-1)

-- | A subscripting function for meta-tags produced by makeMeta
sub :: Meta -> Int -> Meta
sub m n = m {metaColumn = n}

sm0, sm1, sm2, sm3, sm4, sm5, sm6, sm7, sm8, sm9, sm10, sm11 :: A.Process
-- Various abbreviations for unique A.Process items
sm0 = A.Skip m0
sm1 = A.Skip m1
sm2 = A.Skip m2
sm3 = A.Skip m3
sm4 = A.Skip m4
sm5 = A.Skip m5
sm6 = A.Skip m6
sm7 = A.Skip m7
sm8 = A.Skip m8
sm9 = A.Skip m9
sm10 = A.Skip m10
sm11 = A.Skip m11

-- | Shows a graph as a node and edge list.
showGraph :: (Graph g, Show a, Show b) => g a b -> String
showGraph g = " Nodes: " ++ show (labNodes g) ++ " Edges: " ++ show (labEdges g)

-- | A shortcut for nextId' 1.
nextId :: Data t => t -> State (Map.Map Meta Int) Int
nextId = nextId' 1

-- | Given an AST fragment, returns a unique integer associated with that meta-tag.
-- This is for when you may add nodes based on a certain meta-tag to the tree multiple times,
-- and you want to be able to differentiate between each use.
nextId' :: Data t => Int -> t -> State (Map.Map Meta Int) Int
nextId' inc t
  = do mp <- get
       case Map.lookup m mp of
         Just n -> do put $ Map.adjust ((+) inc) m mp
                      return n
         Nothing -> do put $ Map.insert m inc mp
                       return 0
       where m = findMeta t

-- | Given a test name, a list of nodes, a list of root nodes, a list of edges and an AST fragment, tests that the
-- CFG produced from the given AST matches the nodes and edges.  The nodes do not have to have
-- the exact correct identifiers produced by the graph-building.  Instead, the graphs are checked
-- for being isomorphic, based on the meta-tag node labels (node E in the expected list is 
-- isomorphic to node A in the actual list if their meta tags are the same).
testGraph :: String -> [(Int, Meta)] -> [Int] -> [(Int, Int, EdgeLabel)] -> A.Process -> Test
testGraph testName nodes roots edges proc = testGraphF testName nodes roots edges (buildFlowGraphP testOps $ A.Only emptyMeta proc)

testGraph' :: String -> [(Int, Meta)] -> [Int] -> [(Int, Int, EdgeLabel)] -> A.AST -> Test
testGraph' testName nodes roots edges str = testGraphF testName nodes roots edges (buildFlowGraph testOps str)

testOps :: GraphLabelFuncs (State (Map.Map Meta Int)) Int
testOps = GLF nextId nextId nextId nextId nextId nextId nextId (nextId' 100) (nextId' 100)

testGraphF :: Data structType => String -> [(Int, Meta)] -> [Int] -> [(Int, Int, EdgeLabel)] -> State (Map.Map Meta Int) (Either String (FlowGraph' Identity Int structType, [Node])) -> Test
testGraphF testName nodes roots edges grF
  = TestCase $ 
      case evalState grF Map.empty of
        Left err -> assertFailure (testName ++ " graph building failed: " ++ err)
        Right gr -> checkGraphEquality (nodes, roots, edges) gr -- :: (FlowGraph' Identity Int structType, [Node]))
  where  
    -- Checks two graphs are equal by creating a node mapping from the expected graph to the real map (checkNodeEquality),
    -- then mapping the edges across (transformEdge) and checking everything is right (in checkGraphEquality)
    
--    deNode :: Monad m => FNode' m a b -> (Meta, a)
    deNode nd = (getNodeMeta nd, getNodeData nd)
        
    checkGraphEquality :: (Data a, Monad m) => ([(Int, Meta)], [Int], [(Int, Int, EdgeLabel)]) -> (FlowGraph' m Int a, [Int]) -> Assertion
    checkGraphEquality (nodes, roots, edges) (g, actRoots)
      = do let (remainingNodes, nodeLookup, ass) = foldl checkNodeEquality (Map.fromList (map revPair nodes),Map.empty, return ()) (map (transformPair id deNode) $ labNodes g)
           ass
           assertBool (testName ++ " Expected graph had nodes not found in the real graph: " ++ show remainingNodes ++ ", real graph: " ++ showGraph g) (Map.null remainingNodes)
           roots' <- mapM (transformNode nodeLookup) roots
           assertEqual (testName ++ " Root lists not equal") (sort roots') (sort actRoots)
           edges' <- mapM (transformEdge nodeLookup) edges
           assertEqual (testName ++ " Edge lists not equal") (sort $ edges') (sort $ labEdges g)
    
    checkNodeEquality :: (Map.Map Meta Int, Map.Map Int Int, Assertion) -> (Node, (Meta, Int)) -> (Map.Map Meta Int, Map.Map Int Int, Assertion)
    checkNodeEquality (metaToTestId, realToTestId, ass) (nodeId, (metaTag,metaSub))
      = case Map.lookup (sub metaTag metaSub) metaToTestId of
          Nothing -> (metaToTestId, realToTestId, ass >> assertFailure (testName ++ " Node with meta tag " ++ show (sub metaTag metaSub) ++ " not found in expected test data"))
          Just testId -> let realToTestId' = Map.insert testId nodeId realToTestId in
                         let metaToTestId' = Map.delete (sub metaTag metaSub) metaToTestId in
                         (metaToTestId', realToTestId', ass)
    transformEdge :: Show b => Map.Map Int Int -> (Int, Int, b) -> IO (Int, Int, b)
    transformEdge nodeMap e@(start, end, label)
      = case mergeMaybe (Map.lookup start nodeMap) (Map.lookup end nodeMap) of
          Nothing -> do assertFailure ("Could not map test edge to real edge: " ++ show e)
                        return e
          Just (start', end') -> return (start', end', label)

    transformNode :: Map.Map Int Int -> Int -> IO Int
    transformNode m n = case Map.lookup n m of
      Just n' -> return n'
      Nothing -> assertFailure (testName ++ " could not find root node in new graph: " ++ show n) >> return n

-- | A helper function for making simple A.Specification items.
someSpec :: Meta -> A.Specification
someSpec m = A.Specification m (simpleName $ show m) (A.DataType m A.Int)
               
testSeq :: Test
testSeq = TestLabel "testSeq" $ TestList
 [
   testSeq' 0 [(0,m1)] [] (A.Several m1 [])
  ,testSeq' 1 [(0,m2)] [] (A.Only m1 sm2)
  ,testSeq' 2 [(0,m3)] [] (A.Several m1 [A.Only m2 sm3])
  ,testSeq' 3 [(0,m3),(1,m5)] [(0,1,ESeq)] (A.Several m1 [A.Only m2 sm3,A.Only m4 sm5])
  ,testSeq' 4 [(0,m3),(1,m5),(2,m7)] [(0,1,ESeq),(1,2,ESeq)] (A.Several m1 [A.Only m2 sm3,A.Only m4 sm5,A.Only m6 sm7])
  ,testSeq' 5 [(0,m3),(1,m5)] [(0,1,ESeq)] (A.Several m1 [A.Several m1 [A.Only m2 sm3],A.Several m1 [A.Only m4 sm5]])
  ,testSeq' 6 [(0,m3),(1,m5),(2,m7),(3,m9)] [(0,1,ESeq),(1,2,ESeq),(2,3,ESeq)] 
    (A.Several m1 [A.Several m1 [A.Only m2 sm3,A.Only m4 sm5,A.Only m6 sm7], A.Only m8 sm9])
    
  ,testSeq' 10 [(0,m1),(1,m4),(100,sub m1 100)] [(0,1,ESeq),(1,100,ESeq)] (A.Spec mU (someSpec m1) $ A.Only m3 sm4)
  ,testSeq'' 11
    [(1,m1),(3,m4),(5,m5),(7,m7),(9,m10),(101,sub m1 100),(105,sub m5 100),(107,sub m7 100)] [1]
    [(1,3,ESeq),(3,101,ESeq),(101,5,ESeq),(5,7,ESeq),(7,9,ESeq),(9,107,ESeq),(107,105,ESeq)]
    (A.Several m11 [A.Spec mU (someSpec m1) $ A.Only m3 sm4,A.Spec mU (someSpec m5) $ A.Spec mU (someSpec m7) $ A.Only m9 sm10])

  ,testSeq' 12 [(0,m1),(4,m4),(100,sub m1 100)] [(0,4,ESeq),(4,100,ESeq)] (A.Spec mU (someSpec m1) $ A.Several m4 [])

  -- Replicated SEQ:
  
  ,testSeq' 100 [(0,m10), (1,m3), (2,m5)] [(0,1,ESeq), (1,2,ESeq), (2,0,ESeq)]
    (A.Rep m10 (A.For m10 undefined undefined undefined) $ A.Several m1 [A.Only m2 sm3,A.Only m4 sm5])

  ,testSeq'' 101 [(0,m8), (1,m3), (2,m5),(3,m9),(4,m11)] [3] [(3,0,ESeq),(0,1,ESeq), (1,2,ESeq), (2,0,ESeq),(0,4,ESeq)]
    (A.Only mU $ A.Seq m6 $ A.Several m7
      [A.Only mU sm9
      ,(A.Rep m8 (A.For m8 undefined undefined undefined) $ A.Several m1 [A.Only m2 sm3,A.Only m4 sm5])
      ,A.Only mU sm11])

  ,testSeq' 102 [(0,m10), (1,m1)] [(0,1,ESeq), (1,0,ESeq)]
    (A.Rep m10 (A.For m10 undefined undefined undefined) $ A.Several m1 [])

  ,testSeq' 103 [(1,m10), (0,m1), (2,m2), (3,m3)] [(0,1,ESeq),(1,3,ESeq), (3,1,ESeq),(1,2,ESeq)]
    (A.Several mU [A.Only mU sm1, (A.Rep m10 (A.For m10 undefined undefined undefined) $ A.Several m3 []), A.Only mU sm2])

 ]
  where
    testSeq' :: Int -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Structured A.Process -> Test
    testSeq' n a b s = testSeq'' n a [0] b s

    testSeq'' :: Int -> [(Int, Meta)] -> [Int] -> [(Int, Int, EdgeLabel)] -> A.Structured A.Process -> Test
    testSeq'' n a r b s = testGraph ("testSeq " ++ show n) a r b (A.Seq m0 s)
    
testPar :: Test
testPar = TestLabel "testPar" $ TestList
 [
   testPar' 0 [] [(0,99,ESeq)] (A.Several m1 [])
  ,testPar' 1 [(1,m2)] [(0,1,EStartPar 0), (1,99,EEndPar 0)] (A.Only m1 sm2)
  ,testPar' 2 [(1,m3)] [(0,1,EStartPar 0), (1,99,EEndPar 0)] (A.Several m1 [A.Only m2 sm3])
  ,testPar' 3 [(1, m3), (2, m5)]
              [(0,1,EStartPar 0),(1,99,EEndPar 0), (0,2,EStartPar 0), (2,99,EEndPar 0)]
              (A.Several m1 [A.Only m2 sm3,A.Only m4 sm5])
  ,testPar' 4 [(3,m3),(5,m5),(7,m7)]
              [(0,3,EStartPar 0),(3,99,EEndPar 0),(0,5,EStartPar 0),(5,99,EEndPar 0),(0,7,EStartPar 0),(7,99,EEndPar 0)] 
              (A.Several m1 [A.Only m2 sm3,A.Only m4 sm5,A.Only m6 sm7])
  ,testPar' 5 [(1, m3), (2, m5)]
              [(0,1,EStartPar 0),(1,99,EEndPar 0), (0,2,EStartPar 0), (2,99,EEndPar 0)]
              (A.Several mU [A.Several mU [A.Only m2 sm3],A.Several mU [A.Only m4 sm5]])
  ,testPar' 6 [(3,m3),(5,m5),(7,m7),(9,m9)]
              [(0,3,EStartPar 0), (0,5,EStartPar 0), (0,7,EStartPar 0), (0,9,EStartPar 0)
              ,(3,99,EEndPar 0), (5,99,EEndPar 0), (7,99,EEndPar 0), (9,99,EEndPar 0)]
              (A.Several m1 [A.Several m10 [A.Only m2 sm3,A.Only m4 sm5,A.Only m6 sm7], A.Only m8 sm9])

  ,testPar' 10 [(1, m3), (2, m5), (6, m6),(106,sub m6 100)]
               [(0,6,EStartPar 0),(6,1,ESeq),(1,106,ESeq),(106,99,EEndPar 0), (0,2,EStartPar 0), (2,99,EEndPar 0)]
               (A.Several m1 [A.Spec mU (someSpec m6) $ A.Only m2 sm3,A.Only m4 sm5])
  ,testPar' 11 [(1, m3), (2, m5), (3,m7), (6, m6),(106,sub m6 100)]
               [(0,6,EStartPar 0),(6,1,EStartPar 1),(6,2,EStartPar 1),(1,106,EEndPar 1),(2,106,EEndPar 1)
               ,(106,99,EEndPar 0), (0,3,EStartPar 0), (3,99,EEndPar 0)]
               (A.Several m1 [A.Spec mU (someSpec m6) $ A.Several mU [A.Only mU sm3, A.Only mU sm5], A.Only mU sm7])

  ,testPar' 20 [(1,m1),(100,sub m1 100)] [(0,1,EStartPar 0),(1,100,ESeq),(100,99,EEndPar 0)] (A.Spec mU (someSpec m1) $ A.Several m4 [])

  --TODO test nested pars

  
  -- Replicated PAR:
  
  ,testPar' 100 [(1,m6), (2,m3), (3,m5), (4, sub m6 1)]
    [(0,1,EStartPar 0), (1,2,EStartPar 1), (2,4,EEndPar 1), (1,3,EStartPar 1), (3,4,EEndPar 1), (4,99,EEndPar 0)]
    (A.Rep m6 (A.For m6 undefined undefined undefined) $ A.Several m1 [A.Only m2 sm3,A.Only m4 sm5])  

  ,testPar' 101 [(1,m1), (2,m2), (3,m3), (11,sub m1 1), (4,m4), (5,m5), (6,m6), (7,m7), (15, sub m5 1)]
    -- The links in the main PAR:
    [(0,1,EStartPar 0), (11,99,EEndPar 0), (0,4,EStartPar 0), (4,99,EEndPar 0), (0,5,EStartPar 0), (15,99,EEndPar 0)
    -- The links in the first replication:
    ,(1,2,EStartPar 1), (2,11,EEndPar 1), (1,3,EStartPar 1), (3,11,EEndPar 1)
    -- The links in the second replication:
    ,(5,6,EStartPar 2), (6,15,EEndPar 2), (5,7,EStartPar 2), (7,15,EEndPar 2)]
      
    (A.Several mU
      [(A.Rep m1 (A.For m1 undefined undefined undefined) $ A.Several mU [A.Only mU sm2,A.Only mU sm3])
      ,A.Only mU sm4
      ,(A.Rep m5 (A.For m5 undefined undefined undefined) $ A.Several mU [A.Only mU sm6,A.Only mU sm7])])

  ,testPar' 102 [(1,m6), (4, sub m6 1)]
    [(0,1,EStartPar 0), (1,4,ESeq), (4,99,EEndPar 0)]
    (A.Rep m6 (A.For m6 undefined undefined undefined) $ A.Several mU [])
 ]
  where
    testPar' :: Int -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Structured A.Process -> Test
    testPar' n a b s = testGraph ("testPar " ++ show n) (a ++ [(0,m0), (99,sub m0 1)]) [0] b (A.Par m0 A.PlainPar s)

testWhile :: Test
testWhile = TestLabel "testWhile" $ TestList
 [
    testGraph "testWhile 0" [(0,m0), (1,m1)] [0] [(0,1,ESeq), (1,0,ESeq)] (A.While mU (A.True m0) sm1)
   ,testGraph "testWhile 1" [(2,m2), (3, m3), (5, m5)] [2] [(2,3,ESeq), (3,2,ESeq), (2,5,ESeq)] 
      (A.Seq m0 $ A.Several m1 [A.Only m9 $ A.While mU (A.True m2) sm3,A.Only m4 sm5])
   ,testGraph "testWhile 2" [(2,m2), (3, m3), (5, m5), (7, m7)] [7] [(7,2,ESeq), (2,3,ESeq), (3,2,ESeq), (2,5,ESeq)] 
      (A.Seq m0 $ A.Several m1 [A.Only m6 sm7,A.Only m9 $ A.While mU (A.True m2) sm3,A.Only m4 sm5])
   ,testGraph "testWhile 3" [(2,m2), (3, m3), (5, m5), (7, m7), (9, m9)] [7] [(7,2,ESeq), (2,3,ESeq), (3,9,ESeq), (9,2,ESeq), (2,5,ESeq)] 
      (A.Seq m0 $ A.Several m1 [A.Only m6 sm7,A.Only mU $ A.While mU (A.True m2) $ A.Seq mU $ A.Several mU [A.Only mU sm3,A.Only mU sm9],A.Only m4 sm5])
 ]

testCase :: Test
testCase = TestLabel "testCase" $ TestList
 [
   testGraph "testCase 0" [(0,m10),(1,m0),(2,m3)] [0] [(0,2,ESeq),(2,1,ESeq)] (A.Case m0 (A.True m10) $ cases m1 [A.Else m2 sm3])
  ,testGraph "testCase 1"
     [(0,m10),(1,m0),(2,m2),(3,m3)] [0]
     [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq)]
     (A.Case m0 (A.True m10) $ cases mU [A.Option mU [A.True m2] sm3])
  ,testGraph "testCase 2"
     [(0,m10),(1,m0), (2,m2), (3,m3), (4, m4), (5,m5)] [0]
     [(0,2,ESeq), (2,3,ESeq), (3,1,ESeq), (0,4,ESeq), (4,5,ESeq), (5,1,ESeq)]
     (A.Case m0 (A.True m10) $ cases m1 [A.Option mU [A.True m2] sm3, A.Option mU [A.True m4] sm5])
  --TODO test case statements that have specs
 ]
 where
   cases :: Meta -> [A.Option] -> A.Structured A.Option
   cases m = (A.Several m) . (map (A.Only mU))

testIf :: Test
testIf = TestLabel "testIf" $ TestList
 [
   -- Remember that the last branch of an IF doesn't link to the end of the IF, because
   -- occam stops if no option is found.
 
   testGraph "testIf 0" [(0,m0), (1,sub m0 1), (2,m2), (3,m3)] [0] [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq)]
     (A.If m0 $ ifs mU [(A.True m2, sm3)])
  ,testGraph "testIf 1" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (4,m4), (5, m5)] [0]
                        [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq), (2,4,ESeq),(4,5,ESeq),(5,1,ESeq)]
                        (A.If m0 $ ifs mU [(A.True m2, sm3), (A.True m4, sm5)])
  ,testGraph "testIf 2" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (4,m4), (5, m5), (6, m6), (7, m7)] [0]
                        [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq), (2,4,ESeq),(4,5,ESeq),(5,1,ESeq), (4,6,ESeq),(6,7,ESeq),(7,1,ESeq)]
                        (A.If m0 $ ifs mU [(A.True m2, sm3), (A.True m4, sm5), (A.True m6, sm7)])

  ,testGraph "testIf 10" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (5, m5)] [0]
    [(0,5,ESeq), (5,2,ESeq), (2,3,ESeq), (3,1,ESeq), (2, 5, ESeq)]
    (A.If m0 $ A.Rep mU (A.For m5 undefined (A.True mU) (A.True mU)) $ ifs mU [(A.True m2, sm3)])

  ,testGraph "testIf 11" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (5, m5), (6, m6), (7, m7)] [0]
    [(0,5,ESeq), (5,2,ESeq), (2,3,ESeq), (3,1,ESeq), (2, 6, ESeq), (6,7,ESeq), (7,1,ESeq), (6, 5, ESeq)]
    (A.If m0 $ A.Rep mU (A.For m5 undefined (A.True mU) (A.True mU)) $ ifs mU [(A.True m2, sm3), (A.True m6, sm7)])    

  ,testGraph "testIf 12" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (5, m5), (6, m6), (7, m7), (8, m8), (9, m9)] [0]
    [(0,5,ESeq), (5,2,ESeq), (2,3,ESeq), (3,1,ESeq), (2, 6, ESeq), (6,7,ESeq), (7,1,ESeq), (6, 5, ESeq), (5,8,ESeq),
     (8,9,ESeq), (9,1,ESeq)]
    (A.If m0 $ A.Several mU [A.Rep mU (A.For m5 undefined (A.True mU) (A.True mU)) $ ifs mU [(A.True m2, sm3), (A.True m6, sm7)]
                            , ifs mU [(A.True m8, sm9)]])
 ]
 where
   ifs :: Meta -> [(A.Expression, A.Process)] -> A.Structured A.Choice
   ifs m = (A.Several m) . (map (\(e,p) -> A.Only mU $ A.Choice (findMeta e) e p))

testProcFuncSpec :: Test
testProcFuncSpec = TestLabel "testProcFuncSpec" $ TestList
  [
   -- Single spec of process (with SKIP body) in AST (not connected up):
    testGraph' "testProcFuncSpec 0" [(0, m0), (5,m5)] [5] [(5,0,ESeq)]
      (A.Spec mU (A.Specification m1 undefined $ A.Proc m5 undefined undefined sm0) $ A.Several mU [])
      
   -- Single spec of process (with body with SEQ SKIP SKIP):
   ,testGraph' "testProcFuncSpec 1" [(0, m3), (4,m5), (9,m9)] [9] ([(9,0,ESeq), (0,4,ESeq)])
      (A.Spec mU (A.Specification m6 undefined $ A.Proc m9 undefined undefined $
        A.Seq m0 $ A.Several m1 [A.Only m2 sm3,A.Only m4 sm5]
      ) $ A.Several mU [])
   -- Nested spec of process (with bodies with SEQ SKIP SKIP):
   ,testGraph' "testProcFuncSpec 2" [(3,m2),(4,m3),(5,m4),(6,m5), (10,m10), (11, m11)] [10,11]
      ([(10,3,ESeq), (3,4,ESeq)] ++ [(11,5,ESeq), (5,6,ESeq)])
      (A.Spec mU (A.Specification m6 undefined $ A.Proc m10 undefined undefined $
        A.Seq mU $ A.Several mU [A.Only mU sm2,A.Only mU sm3]
      ) $ 
       A.Spec mU (A.Specification m7 undefined $ A.Proc m11 undefined undefined $
        A.Seq mU $ A.Several mU [A.Only mU sm4,A.Only mU sm5]
      )  
      $ A.Several mU [])
      
   -- Single spec of process (with SKIP body) in a SEQ (connected up):
   ,testGraph "testProcFuncSpec 10" [(0, m0),(1,m1),(2,sub m1 100), (3, m3), (5,m5)] [1,5] [(5,0,ESeq), (1,3,ESeq), (3,2,ESeq)]
      (A.Seq mU $ A.Spec mU (A.Specification m1 undefined $ A.Proc m5 undefined undefined sm0) $ A.Several m3 [])
      
  ]

testAlt :: Test
testAlt = TestLabel "testAlt" $ TestList
  [
    -- ALTs have a control-flow pattern of going through all the specs, scoping them in, then
    -- branching to a guard, then doing the guard and body, then scoping everything out.
    
    testGraph "testAlt 0" [(0, m1), (1, sub m1 1), (4,m4), (5,m5)] [0]
      [(0,4,ESeq), (4,5,ESeq), (5,1,ESeq)]
      (A.Alt m1 False $ A.Only mU guard45)
   ,testGraph "testAlt 1" [(0, m1), (1, sub m1 1), (4,m4), (5,m5), (6, m6), (7, m7)] [0]
      [(0,4,ESeq), (0,6,ESeq), (4,5,ESeq), (6,7,ESeq), (5,1,ESeq), (7,1,ESeq)]
      (A.Alt m1 False $ A.Several mU $ map (A.Only mU) [guard45, guard67])

   ,testGraph "testAlt 2" [(0, m1), (1, sub m1 1), (4,m4), (5,m5), (8,m8), (18, sub m8 100)] [0]
      [(0,8,ESeq), (8,4,ESeq), (4,5,ESeq), (5,18,ESeq), (18,1,ESeq)]
      (A.Alt m1 False $ spec8 $ A.Only mU guard45)
   ,testGraph "testAlt 3" [(0, m1), (1, sub m1 1), (4,m4), (5,m5), (8,m8), (18, sub m8 100), (9,m9), (19, sub m9 100)] [0]
      [(0,8,ESeq), (8,9,ESeq), (9,4,ESeq), (4,5,ESeq), (5,19,ESeq), (19,18,ESeq), (18,1,ESeq)]
      (A.Alt m1 False $ spec8 $ spec9 $ A.Only mU guard45)      

   ,testGraph "testAlt 4" [(0, m1), (1, sub m1 1), (4,m4), (5,m5), (6, m6), (7, m7), (8,m8), (18, sub m8 100)] [0]
      [(0,8,ESeq), (8,4,ESeq), (8,6,ESeq), (4,5,ESeq), (6,7,ESeq), (5,18,ESeq), (7,18,ESeq), (18, 1, ESeq)]
      (A.Alt m1 False $ A.Several mU $ [A.Only mU guard45, spec8 $ A.Only mU guard67])

   ,testGraph "testAlt 5" [(0, m1), (1, sub m1 1), (4,m4), (5,m5), (6, m6), (7, m7), (8,m8), (18, sub m8 100), (9,m9), (19, sub m9 100)] [0]
      [(0,9,ESeq), (9,8,ESeq),(8,4,ESeq), (8,6,ESeq), (4,5,ESeq), (6,7,ESeq), (5,18,ESeq), (7,18,ESeq), (18, 19, ESeq), (19,1,ESeq)]
      (A.Alt m1 False $ A.Several mU $ [spec9 $ A.Only mU guard45, spec8 $ A.Only mU guard67])

   -- TODO test replicated ALTs
   -- TODO test specs inside replicated ALTs

  ]
  where
    guard45 = A.AlternativeSkip m4 (A.True mU) sm5
    guard67 = A.Alternative m6 (A.True mU) (variable "c") (A.InputSimple mU []) sm7
    
    spec8 = A.Spec mU (A.Specification m8 undefined undefined)
    spec9 = A.Spec mU (A.Specification m9 undefined undefined)

--TODO occam stuff:
--TODO test input-case statements
--TODO test replicated ifs


-- The idea here is that each time we generate an interesting node,
-- we want to generate its replaced version too.  Then combine these as
-- we go back up the tree to form a set of all possible trees (which is like the powerset of possible replacements, I think).
-- We also want to ensure that the meta tags are unique (to label replacements), and I don't think
-- QuickCheck easily supports that.

-- So how to do this, given that QuickCheck expects something of type Gen a to come
-- back out of Arbitrary?  We could generate Gen [a], with the understanding that the head
-- is the source, all the others are possible replacements.  But then we need to label the replacements,
-- which means we'd want Gen [([Meta],a)]

-- However, in order to ensure we make unique meta tags, we have to add the StateT Int wrapper:

-- | A newtype based on Int, to avoid confusion with other uses of Int.
newtype Id = Id Int

-- | Turns the Id newtype back into a plain Int
fromId :: Id -> Int
fromId (Id n) = n

-- | Similar to makeMeta, but takes an Id as its argument.
makeMeta' :: Id -> Meta
makeMeta' = makeMeta . fromId

-- | The monad type for generating ASTs.  The StateT wrapped is needed for making
-- the meta tags unique, and the reason for the strange generation type is explained in
-- earlier comments.
type GenL a = StateT Id Gen [([Meta], a)]

-- | A helper function for making a simple meta-tag replacement operation.
replaceMeta :: Meta -> Meta
replaceMeta m = sub m 8

-- | Given a meta tag, returns the standard and replaced versions of it.
genMeta :: Meta -> GenL Meta
genMeta m = return [([],m),([m],replaceMeta m)]

-- Helper functions for dealing with the AST:

-- | The genElemN functions take an AST constructor (that has Meta as its first item)
-- then the appropriate Meta tag and optional further arguments, and returns the standard
-- and replaced combinations across all of them using the combN functions.
genElem1 :: (Meta -> b) -> Meta -> GenL b
genElem1 f m = comb1 f (genMeta m)

genElem2 :: (Meta -> a0 -> b) -> Meta -> GenL a0 -> GenL b
genElem2 f m = comb2 f (genMeta m)

genElem3 :: (Meta -> a0 -> a1 -> b) -> Meta -> GenL a0 -> GenL a1 -> GenL b
genElem3 f m = comb3 f (genMeta m) 

genElem4 :: (Meta -> a0 -> a1 -> a2 -> b) -> Meta -> GenL a0 -> GenL a1 -> GenL a2 -> GenL b
genElem4 f m = comb4 f (genMeta m) 

-- | A helper function for turning any item that can't be replaced into a GenL form (esp.
-- for use as a parameter of genElemN).
comb0 :: forall a. a -> GenL a
comb0 x = return [([],x)]

-- | The combN functions (N >= 1) take a constructor, then the appropriate number of GenL
-- items, and works out all possible combinations of replacements and so on.  The number
-- of replacements can get very large (2^K, where K is the number of GenL parameters that
-- can be replaced).
comb1 :: forall a0 b. (a0 -> b) -> GenL a0 -> GenL b
comb1 func list0 = list0 >>* map process1
  where
    process1 :: ([Meta], a0) -> ([Meta],b)
    process1 = transformPair id func

comb2 :: forall a0 a1 b. (a0 -> a1 -> b) -> GenL a0 -> GenL a1 -> GenL b
comb2 func list0 list1 = (liftM2 (,)) list0 list1 >>* product2 >>* map (uncurry process2)
  where
    process2 :: ([Meta], a0) -> ([Meta], a1) -> ([Meta],b)
    process2 (keys0, val0) (keys1, val1) = (keys0++keys1, func val0 val1)
    
comb3 :: forall a0 a1 a2 b. (a0 -> a1 -> a2 -> b) -> GenL a0 -> GenL a1 -> GenL a2 -> GenL b
comb3 func list0 list1 list2 = (liftM3 (,,)) list0 list1 list2 >>* product3 >>* map (uncurry3 process3)
  where
    process3 :: ([Meta], a0) -> ([Meta], a1) -> ([Meta],a2) -> ([Meta],b)
    process3 (keys0, val0) (keys1, val1) (keys2, val2) = (keys0++keys1++keys2, func val0 val1 val2)

comb4 :: forall a0 a1 a2 a3 b. (a0 -> a1 -> a2 -> a3 -> b) -> GenL a0 -> GenL a1 -> GenL a2 -> GenL a3 -> GenL b
comb4 func list0 list1 list2 list3 = (liftM4 (,,,)) list0 list1 list2 list3 >>* product4 >>* map (uncurry4 process4)
  where
    process4 :: ([Meta], a0) -> ([Meta], a1) -> ([Meta],a2) -> ([Meta],a3) -> ([Meta],b)
    process4 (keys0, val0) (keys1, val1) (keys2, val2) (keys3, val3) = (keys0++keys1++keys2++keys3, func val0 val1 val2 val3)

-- | Wrapper for Quickcheck.
-- In order to stop conflict with Quickcheck's in-built rules for things such as pairs
-- (which do not allow overlapping instances), we have to wrap such types ourself.
newtype QC a = QC a deriving (Eq)

-- | We don't allow size zero for generating trees.
-- So we cheat by changing the size to 1, if it is 0.
enforceSize1 :: Gen a -> Gen a
enforceSize1 f = sized $ \n -> if n == 0 then resize 1 f else f

-- | An instance of Arbitrary for A.Structured that wraps the "genStructured" function.
instance Arbitrary (QC (A.Process, Map.Map [Meta] A.Process)) where
  arbitrary = enforceSize1 $ sized $ \n -> evalStateT (genProcess n) (Id 0) >>* findEmpty >>* QC
    where
      -- Copies the value for the empty-list key into the first element of the tuple:
      findEmpty :: [([Meta], a)] -> (a, Map.Map [Meta] a)
      findEmpty xs = (fromJust $ Map.lookup [] m, m)
        where m = Map.fromList xs

  -- coarbitrary is for defined "twiddle" functions over data generated by arbitrary.
  -- For example, we could have the twiddle functions changing an expression
  -- in the tree.  I don't think this would be of use right now, given what we're testing

instance Show (QC (A.Process, Map.Map [Meta] A.Process)) where
  show (QC (p,m)) = pshow (p,nub $ concat $ Map.keys m)

-- | A function inside a StateT monad that returns the next unique Id.
nextIdT :: Monad m => StateT Id m Id
nextIdT = modify' incId
  where
    incId :: Id -> Id
    incId (Id n) = (Id $ n+1)

-- | A function similar to the QuickCheck oneof function, that works on GenL stuff rather than Gen.
oneofL :: [GenL a] -> GenL a
oneofL [] = fail "Empty list fed to oneofL"
oneofL gs = do i <- lift $ choose (0,length gs-1)
               gs !! i

-- | A function that takes in a list of sized items.  The first thing in the pair is the minimum size
-- of an item produced, and the second is a function that maps a size into a GenL.  One of these
-- functions is chosen and returned, with the obvious constraint that only generators whose
-- minimum size is satisfied will be called.
--
-- TODO at the moment I think I've generally estimated size.  Size should refer to the number of items
-- that can potentially be replaced, but I'm not sure that is always strictly kept to.  Still, it's
-- a close enough approximation.
oneofLS :: [(Int, Int -> GenL a)] -> Int -> GenL a
oneofLS fs n = oneofL $ applyAll n filtered
  where
    filtered = filterFuncs n fs
  
    filterFuncs :: Int -> [(Int, Int -> GenL a)] -> [Int -> GenL a]
    filterFuncs sz = map snd . filter ((<= sz) . fst)

-- | A function that takes a "find" parameter, a "replace" parameter, and returns a monadic function
-- (for convenience) that performs the check\/replacement.
replaceM :: (Eq a, Monad m) => a -> a -> (a -> m a)
replaceM find replace x | find == x = return replace
                        | otherwise = return x

-- | A little helper function for generating random lists of numbers.  Given a total,
-- this generates a list of random numbers that sum to that total.  The function is of course recursive,
-- and each number is between 1 and the remaining total (evenly distributed).  This does mean
-- that the earlier items in the list will tend to be larger than the later items, and I think
-- there is a high chance of the last item in the list being 1.  But hopefully for our tests this
-- isn't major limitation.
genNumsToTotal :: Int -> Gen [Int]
genNumsToTotal 0 = return []
genNumsToTotal n = do ch <- choose (1,n)
                      chs <- genNumsToTotal (n-ch)
                      return (ch:chs)

-- | A function that takes a generator for an item, and generates a list of those,
-- dividing up the size at random.  The list will be length log_2(N) on average, I think.
genList :: (Int -> GenL a) -> Int -> GenL [a]
genList _ 0 = return [([],[])]
genList f n = (lift $ genNumsToTotal n) >>= mapM f >>= foldList
  where
    foldList :: [[([Meta], a)]] -> StateT Id Gen [([Meta], [a])]
    foldList [g] = comb1 singleton (return g)
    foldList gs = return $ foldr foldX [] gs
    
    foldX :: [([Meta], a)] -> [([Meta], [a])] -> [([Meta], [a])]
    foldX xs [] = map (uncurry mix) (zip xs $ repeat ([],[]))
    foldX xs ys = map (uncurry mix) (product2 (xs,ys))
    
    mix :: ([Meta], a) -> ([Meta], [a]) -> ([Meta], [a])
    mix (ms0,x) (ms1,xs) = (ms0++ms1,x:xs)

-- Helper functions for subtraction.
sub1 :: Int -> Int
sub1 x = x-1

sub2 :: Int -> Int
sub2 x = x-2

sub3 :: Int -> Int
sub3 x = x-3

-- Be careful with the test generators; there should always be an option with value 1 (or 0)
-- in every list.  Recursion should always decrease the test size, and you
-- should take the recursion into account in the required size (generally, recursive
-- generators will have value 2 at least).  If you cannot have something of size 1 in the list,
-- (such as for A.Alternative) you need to take account of this in its parent items, and bump
-- up the required size for them accordingly.

-- | Generates a simple expression (A.True m).
genExpression :: GenL A.Expression
genExpression = nextIdT >>* makeMeta' >>= genElem1 A.True

-- | Generates a simple, empty, expression list.
genExpressionList :: GenL A.ExpressionList
genExpressionList = nextIdT >>* makeMeta' >>= (flip $ genElem2 A.ExpressionList) (comb0 [])

-- | Generates an A.Alternative.  Currently always A.AlternativeSkip.
genAlternative :: Int -> GenL A.Alternative
genAlternative n = nextIdT >>* makeMeta' >>= \m -> (flip oneofLS) n
  [
    (3, genElem3 A.AlternativeSkip m genExpression . genProcess . sub2)
  ]

genAlternative' :: (Int, Int -> GenL A.Alternative)
genAlternative' = (3, genAlternative)

-- | Generates a A.Specification.
genSpecification :: GenL A.Specification
genSpecification = nextIdT >>* makeMeta' >>= \m -> genElem3 A.Specification m (comb0 $ simpleName "x") genSpecType
  where
    genSpecType :: GenL A.SpecType
    genSpecType = nextIdT >>* makeMeta' >>= \m -> oneofL
      [
        genElem2 A.Declaration m (comb0 A.Int)
       ,genElem2 A.Declaration m (comb0 A.Int)
       ,genElem2 (\m e -> A.IsExpr m A.ValAbbrev A.Int e) m genExpression
       --TODO proc and function declaration
      ]

genChoice :: Int -> GenL A.Choice
genChoice n = nextIdT >>* makeMeta' >>= \m -> (comb2 (\e p -> A.Choice emptyMeta e p) genExpression . genProcess . sub2) n

genChoice' :: (Int, Int -> GenL A.Choice)
genChoice' = (3, genChoice)

genOption :: Int -> GenL A.Option
genOption = comb1 (A.Else emptyMeta) . genProcess

genOption' :: (Int, Int -> GenL A.Option)
genOption' = (1, genOption)

genReplicator :: GenL A.Replicator
genReplicator = nextIdT >>* makeMeta' >>= \m -> genElem4 A.For m (comb0 $ simpleName "i") genExpression genExpression

class ReplicatorAnnotation a where
  replicatorItem :: (Int, Int -> GenL a) -> Maybe (Int, Int -> GenL (A.Structured a))

replicatorItem' :: (ReplicatorAnnotation a, Data a) => (Int, Int -> GenL a) -> (Int, Int -> GenL (A.Structured a))
replicatorItem' x = (4, comb2 (A.Rep emptyMeta) genReplicator . genStructured x . sub3)

   --Replicators are allowed in ALTs, IFs, SEQs and PARs:
instance ReplicatorAnnotation A.Process where replicatorItem = Just . replicatorItem'
instance ReplicatorAnnotation A.Alternative where replicatorItem = Just . replicatorItem'
instance ReplicatorAnnotation A.Choice where replicatorItem = Just . replicatorItem'

instance ReplicatorAnnotation A.Option where replicatorItem = const Nothing

-- | Generates a A.Structured, obeying the given OnlyAllowed structure.
genStructured :: (Data a, ReplicatorAnnotation a) => (Int, Int -> GenL a) -> Int -> GenL (A.Structured a)
genStructured (no,genOnly) n = nextIdT >>* makeMeta' >>= \m -> (flip oneofLS) n
 ([{-
    cond (onlyP allowed) (2,genElem2 A.Only m . genProcess . sub1 )
   ,cond (onlyO allowed) (2,comb1 (A.Only emptyMeta . A.Else emptyMeta) . genProcess . sub1 )
   ,cond (onlyC allowed) (3,comb2 (\e p -> A.Only emptyMeta $ A.Choice emptyMeta e p) genExpression . genProcess . sub2)
   ,cond (onlyA allowed) (4,genElem2 A.Only m . genAlternative . sub1 )
-}   
   -- As below, we subtract one to ensure termination
   (no + 1, comb1 (A.Only m) . genOnly . sub1)

   -- Specs currently don't work with Case statements TODO
   ,(3,genElem3 A.Spec m genSpecification . genStructured (no, genOnly) . sub2 )
   
   -- We don't have to subtract 1 here, but we do to ensure test termination
   -- Otherwise we could infinitely nest Seqs with Severals with Only Seqs with Severals...
   ,(1,comb1 (A.Several emptyMeta) . genList (genStructured (no, genOnly)) . sub1)
  ] ++ maybeToList (replicatorItem (no,genOnly)) )

-- | Generates a A.Process.
genProcess :: Int -> GenL A.Process
genProcess n = nextIdT >>* makeMeta' >>= \m -> (flip oneofLS) n
  [
    (1,const $ genElem1 A.Skip m)
   ,(1,const $ genElem1 A.Stop m)
   ,(1,comb1 (A.Seq emptyMeta) . genStructured genProcess')
   ,(1,comb1 (A.Par emptyMeta A.PlainPar) . genStructured genProcess')
   ,(3,genElem3 A.While m genExpression . genProcess . sub2)
   ,(1,comb1 (A.If emptyMeta) . genStructured genChoice')
   ,(2,comb2 (A.Case emptyMeta) genExpression . genStructured genOption' . sub1)
   ,(2,const $ genElem3 A.Assign m (comb0 [variable "x"]) genExpressionList)
   ,(2,comb1 (A.Alt emptyMeta True) . genStructured genAlternative' . sub1)
  ]

genProcess' :: (Int, Int -> GenL A.Process)
genProcess' = (1, genProcess)

-- | Generates a flow-graph from the given AST.
-- TODO put this in proper error monad
genGraph :: A.Structured A.Process -> FlowGraph' Identity () A.Process
genGraph s = either (\e -> error $ "QuickCheck graph did not build properly: " ++ e ++ ", from: " ++ pshow s) fst $ runIdentity $ buildFlowGraphP funcs s
  where
    funcs :: GraphLabelFuncs Identity ()
    funcs = mkLabelFuncsConst (return ())

-- | Given a flow-graph, it returns a list of all the identity alteration functions,
-- for each node.  Applying any, many or all of these functions to the source AST
-- should leave it unchanged.
pickFuncId :: (Data a, Monad m) => FlowGraph' m () a -> [A.Structured a -> m (A.Structured a)]
pickFuncId g = map (applyFunc . getFunc) (labNodes g)
  where
    getFunc (_,n) = getNodeFunc n
    
    applyFunc (AlterAlternative f) = f return
    applyFunc (AlterProcess f) = f return
    applyFunc (AlterExpression f) = f return
    applyFunc (AlterExpressionList f) = f return
    applyFunc (AlterReplicator f) = f return
    applyFunc (AlterSpec f) = f return
    applyFunc (AlterNothing) = return

-- | Given a flow-graph, it returns a list of the meta-tag replacement alteration functions,
-- for each meta-tag (i.e. each node).
pickFuncRep :: (Data a, Monad m) => FlowGraph' m () a -> Map.Map Meta (A.Structured a -> m (A.Structured a))
pickFuncRep gr = Map.fromList $ filter ((/= emptyMeta) . fst) $ map (helpApplyFunc . getMetaFunc) (labNodes gr)
  where
    getMetaFunc (_,n) = (getNodeMeta n,getNodeFunc n)
    
    helpApplyFunc (m,f) = (m, applyFunc (m,f))
    
    applyFunc (m,AlterAlternative f) = f (g m)
    applyFunc (m,AlterProcess f) = f (g m)
    applyFunc (m,AlterExpression f) = f (g m)
    applyFunc (m,AlterExpressionList f) = f (g m)
    applyFunc (m,AlterReplicator f) = f (g m)
    applyFunc (m,AlterSpec f) = f (g m)
    applyFunc (m,AlterNothing) = return
    
    g m = gmapM (mkM $ replaceM m (replaceMeta m))


-- | It is important to have these functions in the right ratio.  The number of possible trees is
-- 2^N, where N is the test size.  Therefore I suggest keeping N <= 10 as a sensible limit.
-- Hence, if there are 1000 tests, we divide the test number by 100 to get the test size.
configForSize :: Int -> Config
configForSize n = defaultConfig { configMaxTest = n, configSize = \x -> x `div` scale }
  where
    scale = n `div` 10

deepCheck :: Testable a => a -> QuickCheckTest
deepCheck test level = (flip testCheck) test $ configForSize $
  case level of 
    QC_Low -> 100
    QC_Medium -> 1000
    QC_High -> 5000
    QC_Extensive -> 10000

testModify :: [LabelledQuickCheckTest]
testModify =
 [
   ("Control-Flow Graph Identity Transformations", deepCheck (runTest . prop_Id))
  ,("Control-Flow Graph Replacement Transformations", deepCheck (runTest . prop_Rep))
  ,("Random List Generation", deepCheck (runTest . prop_gennums))
 ]
  where
    -- | Checks that applying any set (from the powerset of identity functions) of identity functions
    -- does not change the AST.
    prop_Id :: QC (A.Process, Map.Map [Meta] A.Process) -> QCProp
    prop_Id (QC (g,_)) = sequence_ $ (flip map) (map (foldFuncsM) $ powerset $ pickFuncId $ genGraph g') $ \f -> runIdentity (f g') *==* g'
      where
        g' = A.Only emptyMeta g

    -- | Checks that applying any set (from the powerset of replacement functions) of replacement functions
    -- produces the expected result.
    prop_Rep :: QC (A.Process, Map.Map [Meta] A.Process) -> QCProp
    prop_Rep (QC (g,rest)) = sequence_ $ (flip map) (helper $ pickFuncRep $ genGraph g') $ 
        \(funcs,ms) -> testEqual (show ms)
          (Just (runIdentity (applyMetas ms funcs g'))) (Map.lookup ms rest >>* A.Only emptyMeta)
      where
        g' = A.Only emptyMeta g
  
    -- | This tests our genNumsToTotal function, which is itself a test generator; nasty!
    prop_gennums :: Int -> QCProp
    prop_gennums n = generate 0 (mkStdGen 0) (genNumsToTotal n >>* sum) *==* n

    -- | Repeatedly pairs the map with each element of the powerset of its keys
    helper :: Monad m => Map.Map Meta (A.Structured a -> m (A.Structured a)) -> [(Map.Map Meta (A.Structured a -> m (A.Structured a)), [Meta])]
    helper fs = zip (repeat fs) (powerset $ Map.keys fs)

    -- | Applies the functions associated with the given meta tags
    applyMetas :: Monad m => [Meta] -> Map.Map Meta (A.Structured a -> m (A.Structured a)) -> (A.Structured a -> m (A.Structured a))
    applyMetas ms funcs = foldFuncsM $ concatMap (\m -> Map.lookup m funcs) ms

-- | Returns the list of tests:
qcTests :: (Test, [LabelledQuickCheckTest])
qcTests = (TestLabel "FlowGraphTest" $ TestList
 [
   testAlt
  ,testCase
  ,testIf
  ,testPar
  ,testProcFuncSpec
  ,testSeq
  ,testWhile
 ]
 ,testModify)

