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
import TestUtil
import Utils

makeMeta :: Int -> Meta
makeMeta n = Meta (Just "FlowGraphTest") n 0

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
-- For meta tags that shouldn't be used in the graph:
mU = makeMeta (-1)

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
sm8 = A.Skip m8
sm9 = A.Skip m9
sm10 = A.Skip m10

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
    
    deNode :: FNode a -> (Meta, a)
    deNode (Node x) = x
    
    mapPair :: (x -> a) -> (y -> b) -> (x,y) -> (a,b)
    mapPair f g (x,y) = (f x, g y)
    
    checkGraphEquality :: (Graph g, Show b, Ord b) => ([(Int, Meta)], [(Int, Int, b)]) -> g (FNode Int) b -> Assertion
    checkGraphEquality (nodes, edges) g
      = do let (remainingNodes, nodeLookup, ass) = foldl checkNodeEquality (Map.fromList (map revPair nodes),Map.empty, return ()) (map (mapPair id deNode) $ labNodes g)
           ass
           assertBool (testName ++ " Test graph had nodes not found in the real graph: " ++ show remainingNodes ++ ", real graph: " ++ showGraph g) (Map.null remainingNodes)
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

someSpec :: Meta -> A.Specification
someSpec m = A.Specification m (simpleName $ show m) undefined
               
testSeq :: Test
testSeq = TestList
 [
   testSeq' 0 [(0,m1)] [] (A.Several m1 [])
  ,testSeq' 1 [(0,m2)] [] (A.OnlyP m1 sm2)
  ,testSeq' 2 [(0,m3)] [] (A.Several m1 [A.OnlyP m2 sm3])
  ,testSeq' 3 [(0,m3),(1,m5)] [(0,1,ESeq)] (A.Several m1 [A.OnlyP m2 sm3,A.OnlyP m4 sm5])
  ,testSeq' 4 [(0,m3),(1,m5),(2,m7)] [(0,1,ESeq),(1,2,ESeq)] (A.Several m1 [A.OnlyP m2 sm3,A.OnlyP m4 sm5,A.OnlyP m6 sm7])
  ,testSeq' 5 [(0,m3),(1,m5)] [(0,1,ESeq)] (A.Several m1 [A.Several m1 [A.OnlyP m2 sm3],A.Several m1 [A.OnlyP m4 sm5]])
  ,testSeq' 6 [(0,m3),(1,m5),(2,m7),(3,m9)] [(0,1,ESeq),(1,2,ESeq),(2,3,ESeq)] 
    (A.Several m1 [A.Several m1 [A.OnlyP m2 sm3,A.OnlyP m4 sm5,A.OnlyP m6 sm7], A.OnlyP m8 sm9])
    
  ,testSeq' 10 [(0,m1),(1,m4)] [(0,1,ESeq)] (A.Spec m1 (someSpec m2) $ A.OnlyP m3 sm4)
  ,testSeq' 11 [(1,m1),(3,m4),(5,m5),(7,m7),(9,m10)] [(1,3,ESeq),(3,5,ESeq),(5,7,ESeq),(7,9,ESeq)] 
    (A.Several m11 [A.Spec m1 (someSpec m2) $ A.OnlyP m3 sm4,A.Spec m5 (someSpec m6) $ A.Spec m7 (someSpec m8) $ A.OnlyP m9 sm10])
 ]
  where
    testSeq' :: Int -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Structured -> Test
    testSeq' n a b s = testGraph ("testSeq " ++ show n) a b (A.Seq m0 s)
    
testPar :: Test
testPar = TestList
 [
   testPar' 0 [(0,m1)] [] (A.Several m1 [])
  ,testPar' 1 [(0,m2)] [] (A.OnlyP m1 sm2)
  ,testPar' 2 [(0,m3)] [] (A.Several m1 [A.OnlyP m2 sm3])
  ,testPar' 3 [(0,m1), (1, m3), (2, m5), (3,sub m1 1)]
              [(0,1,EStartPar 0),(1,3,EEndPar 0), (0,2,EStartPar 0), (2,3,EEndPar 0)]
              (A.Several m1 [A.OnlyP m2 sm3,A.OnlyP m4 sm5])
  ,testPar' 4 [(0,m1), (1,sub m1 1), (3,m3),(5,m5),(7,m7)]
              [(0,3,EStartPar 0),(3,1,EEndPar 0),(0,5,EStartPar 0),(5,1,EEndPar 0),(0,7,EStartPar 0),(7,1,EEndPar 0)] 
              (A.Several m1 [A.OnlyP m2 sm3,A.OnlyP m4 sm5,A.OnlyP m6 sm7])
  ,testPar' 5 [(0,m1), (1, m3), (2, m5), (3,sub m1 1)]
              [(0,1,EStartPar 0),(1,3,EEndPar 0), (0,2,EStartPar 0), (2,3,EEndPar 0)]
              (A.Several m1 [A.Several m1 [A.OnlyP m2 sm3],A.Several m1 [A.OnlyP m4 sm5]])
  ,testPar' 6 [(0,m1), (1,sub m1 1),(3,m3),(5,m5),(7,m7),(9,m9),(10,m10),(11,sub m10 1)]
              [(10,3,EStartPar 0),(10,5,EStartPar 0),(10,7,EStartPar 0),(3,11,EEndPar 0),(5,11,EEndPar 0),(7,11,EEndPar 0)
              ,(0,10,EStartPar 1),(11,1,EEndPar 1),(0,9,EStartPar 1),(9,1,EEndPar 1)] 
              (A.Several m1 [A.Several m10 [A.OnlyP m2 sm3,A.OnlyP m4 sm5,A.OnlyP m6 sm7], A.OnlyP m8 sm9])

  ,testPar' 10 [(0,m1), (1, m3), (2, m5), (3,sub m1 1), (4, m6)]
               [(0,4,EStartPar 0),(4,1,ESeq),(1,3,EEndPar 0), (0,2,EStartPar 0), (2,3,EEndPar 0)]
               (A.Several m1 [A.Spec m6 (someSpec m7) $ A.OnlyP m2 sm3,A.OnlyP m4 sm5])
  --TODO test nested pars
 ]
  where
    testPar' :: Int -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Structured -> Test
    testPar' n a b s = testGraph ("testPar " ++ show n) a b (A.Par m0 A.PlainPar s)

testWhile :: Test
testWhile = TestList
 [
    testGraph "testWhile 0" [(0,m0), (1,m1)] [(0,1,ESeq), (1,0,ESeq)] (A.While m0 (A.True m10) sm1)
   ,testGraph "testWhile 1" [(2,m2), (3, m3), (5, m5)] [(2,3,ESeq), (3,2,ESeq), (2,5,ESeq)] 
      (A.Seq m0 $ A.Several m1 [A.OnlyP m9 $ A.While m2 (A.True m10) sm3,A.OnlyP m4 sm5])
   ,testGraph "testWhile 2" [(2,m2), (3, m3), (5, m5), (7, m7)] [(7,2,ESeq), (2,3,ESeq), (3,2,ESeq), (2,5,ESeq)] 
      (A.Seq m0 $ A.Several m1 [A.OnlyP m6 sm7,A.OnlyP m9 $ A.While m2 (A.True m10) sm3,A.OnlyP m4 sm5])
   ,testGraph "testWhile 3" [(2,m2), (3, m3), (5, m5), (7, m7), (9, m9)] [(7,2,ESeq), (2,3,ESeq), (3,9,ESeq), (9,2,ESeq), (2,5,ESeq)] 
      (A.Seq m0 $ A.Several m1 [A.OnlyP m6 sm7,A.OnlyP mU $ A.While m2 (A.True mU) $ A.Seq mU $ A.Several mU [A.OnlyP mU sm3,A.OnlyP mU sm9],A.OnlyP m4 sm5])
 ]

testCase :: Test
testCase = TestList
 [
   testGraph "testCase 0" [(0,m10),(1,m0),(2,m3)] [(0,2,ESeq),(2,1,ESeq)] (A.Case m0 (A.True m10) $ cases m1 [A.Else m2 sm3])
  ,testGraph "testCase 1"
     [(0,m10),(1,m0),(2,m2),(3,m3)]
     [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq)]
     (A.Case m0 (A.True m10) $ cases m1 [A.Option m2 [A.True mU] sm3])
  ,testGraph "testCase 2"
     [(0,m10),(1,m0),(2,m2),(3,m3),(4,m4),(5,m5)]
     [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq), (0,4,ESeq),(4,5,ESeq),(5,1,ESeq)]
     (A.Case m0 (A.True m10) $ cases m1 [A.Option m2 [A.True mU] sm3, A.Option m4 [A.True mU] sm5])
  --TODO test case statements that have specs
 ]
 where
   cases :: Meta -> [A.Option] -> A.Structured
   cases m = (A.Several m) . (map (A.OnlyO mU))

testIf :: Test
testIf = TestList
 [
   testGraph "testIf 0" [(0,m0), (1,sub m0 1), (2,m2), (3,m3)] [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq)]
     (A.If m0 $ ifs mU [(A.True m2, sm3)])
  ,testGraph "testIf 1" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (4,m4), (5, m5)] 
                        [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq), (2,4,ESeq),(4,5,ESeq),(5,1,ESeq)]
                        (A.If m0 $ ifs mU [(A.True m2, sm3), (A.True m4, sm5)])
  ,testGraph "testIf 2" [(0,m0), (1,sub m0 1), (2,m2), (3,m3), (4,m4), (5, m5), (6, m6), (7, m7)] 
                        [(0,2,ESeq),(2,3,ESeq),(3,1,ESeq), (2,4,ESeq),(4,5,ESeq),(5,1,ESeq), (4,6,ESeq),(6,7,ESeq),(7,1,ESeq)]
                        (A.If m0 $ ifs mU [(A.True m2, sm3), (A.True m4, sm5), (A.True m6, sm7)])
 ]
 where
   ifs :: Meta -> [(A.Expression, A.Process)] -> A.Structured
   ifs m = (A.Several m) . (map (\(e,p) -> A.OnlyC mU $ A.Choice (findMeta e) e p))

--TODO test replicated seq/par
--TODO test alts

--TODO occam stuff:
--TODO test input-case statements
--TODO test replicated ifs

--Returns the list of tests:
tests :: Test
tests = TestList
 [
  testCase
  ,testIf
  ,testPar
  ,testSeq
  ,testWhile
 ]
