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

import Control.Monad.Identity
import Control.Monad.State

import Data.Generics
import Data.Graph.Inductive
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Test.HUnit hiding (Node, State)
import Test.QuickCheck

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
nextId = nextId' 1

nextId' :: Data t => Int -> t -> State (Map.Map Meta Int) Int
nextId' inc t
  = do mp <- get
       case Map.lookup m mp of
         Just n -> do put $ Map.adjust ((+) inc) m mp
                      return n
         Nothing -> do put $ Map.insert m inc mp
                       return 0
       where m = findMeta t

testGraph :: String -> [(Int, Meta)] -> [(Int, Int, EdgeLabel)] -> A.Process -> Test
testGraph testName nodes edges proc
  = TestCase $ 
      case evalState (buildFlowGraph testOps (A.OnlyP emptyMeta proc)) Map.empty of
        Left err -> assertFailure (testName ++ " graph building failed: " ++ err)
        Right g -> checkGraphEquality (nodes, edges) g
  where  
    -- Checks two graphs are equal by creating a node mapping from the expected graph to the real map (checkNodeEquality),
    -- then mapping the edges across (transformEdge) and checking everything is right (in checkGraphEquality)
    
    deNode :: Monad m => FNode m a -> (Meta, a)
    deNode (Node (x,y,_)) = (x,y)
    
    testOps :: GraphLabelFuncs (State (Map.Map Meta Int)) Int
    testOps = GLF nextId nextId nextId nextId (nextId' 100) (nextId' 100)
    
    checkGraphEquality :: (Graph g, Show b, Ord b, Monad m) => ([(Int, Meta)], [(Int, Int, b)]) -> g (FNode m Int) b -> Assertion
    checkGraphEquality (nodes, edges) g
      = do let (remainingNodes, nodeLookup, ass) = foldl checkNodeEquality (Map.fromList (map revPair nodes),Map.empty, return ()) (map (transformPair id deNode) $ labNodes g)
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
    
  ,testSeq' 10 [(0,m1),(1,m4),(100,sub m1 100)] [(0,1,ESeq),(1,100,ESeq)] (A.Spec m1 (someSpec m2) $ A.OnlyP m3 sm4)
  ,testSeq' 11
    [(1,m1),(3,m4),(5,m5),(7,m7),(9,m10),(101,sub m1 100),(105,sub m5 100),(107,sub m7 100)]
    [(1,3,ESeq),(3,101,ESeq),(101,5,ESeq),(5,7,ESeq),(7,9,ESeq),(9,107,ESeq),(107,105,ESeq)]
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

  ,testPar' 10 [(0,m1), (1, m3), (2, m5), (3,sub m1 1), (6, m6),(106,sub m6 100)]
               [(0,6,EStartPar 0),(6,1,ESeq),(1,106,ESeq),(106,3,EEndPar 0), (0,2,EStartPar 0), (2,3,EEndPar 0)]
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


-- The idea here is that each type we generate an interesting node,
-- we want to generate its replaced version too.  Then combine these as
-- we go back up the tree to form a set of all possible trees (which is like the powerset of possible replacements, I think).
-- We also want to ensure that the meta tags are unique (to label replacements), and I don't think
-- QuickCheck easily supports that.

-- So how to do this, given that QuickCheck expects something of type Gen a to come
-- back out of Arbitrary?  We could generate Gen [a], with the understanding that the head
-- is the source, all the others are possible replacements.  But then we need to label the replacements,
-- which means we'd want Gen [([Meta],a)]

-- However, in order to ensure we make unique meta tags, we have to add the StateT Int wrapper:

newtype Id = Id Int

fromId :: Id -> Int
fromId (Id n) = n

makeMeta' :: Id -> Meta
makeMeta' = makeMeta . fromId
      
type GenL a = StateT Id Gen [([Meta], a)]

replaceMeta :: Meta -> Meta
replaceMeta m = sub m 8

genMeta :: Meta -> GenL Meta
genMeta m = return [([],m),([m],replaceMeta m)]

-- Helper functions for dealing with the AST:

genElem1 :: (Meta -> b) -> Meta -> GenL b
genElem1 f m = comb1 f (genMeta m) --return [([],f m),([m],f $ replaceMeta m)]

genElem2 :: (Meta -> a0 -> b) -> Meta -> GenL a0 -> GenL b
genElem2 f m = comb2 f (genMeta m)

genElem3 :: (Meta -> a0 -> a1 -> b) -> Meta -> GenL a0 -> GenL a1 -> GenL b
genElem3 f m = comb3 f (genMeta m) 


comb0 :: forall a. a -> GenL a
comb0 x = return [([],x)]

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

-- | Wrapper for Quickcheck.
-- In order to stop conflict with Quickcheck's in-built rules for things such as pairs
-- (which do not allow overlapping instances), we have to wrap such types ourself.
newtype QC a = QC a deriving (Eq, Show)

instance Arbitrary (QC (A.Structured, Map.Map [Meta] A.Structured)) where
  arbitrary = evalStateT genStructured (Id 0) >>* findEmpty >>* QC
    where
      -- Copies the value for the empty-list key into the first element of the tuple:
      findEmpty :: [([Meta], a)] -> (a, Map.Map [Meta] a)
      findEmpty xs = (fromJust $ Map.lookup [] m, m)
        where m = Map.fromList xs

  -- coarbitrary is for defined "twiddle" functions over data generated by arbitrary.
  -- For example, we could have the twiddle functions changing an expression
  -- in the tree.  I don't think this would be of use right now, given what we're testing

nextIdT :: Monad m => StateT Id m Id
nextIdT = modify' incId
  where
    incId :: Id -> Id
    incId (Id n) = (Id $ n+1)

oneofL :: [GenL a] -> GenL a
oneofL gs = do i <- lift $ choose (0,length gs-1)
               gs !! i

replaceM :: (Eq a, Monad m) => a -> a -> (a -> m a)
replaceM find replace x | find == x = return replace
                        | otherwise = return x


genStructured :: GenL A.Structured
genStructured = nextIdT >>* makeMeta' >>= \m -> oneofL
  [
    genElem2 A.OnlyP m genProcess
    -- TODO A.Several m []
  ]


genProcess :: GenL A.Process
genProcess = nextIdT >>* makeMeta' >>= \m -> oneofL
  [
    genElem1 A.Skip m
   ,genElem1 A.Stop m
  ]


-- TODO put this in proper error monad
genGraph :: A.Structured -> FlowGraph Identity ()
genGraph s = either (const $ error "QuickCheck graph did not build properly") id $ runIdentity $ buildFlowGraph funcs s
  where
    empty = const (return ())
    funcs = GLF empty empty empty empty empty empty 

pickFuncId :: Monad m => FlowGraph m () -> [A.Structured -> m A.Structured]
pickFuncId g = map (applyFunc . getFunc) (labNodes g)
  where
    getFunc (_,Node (_,_,f)) = f
    
    applyFunc (AlterProcess f) = f return
    applyFunc (AlterExpression f) = f return
    applyFunc (AlterExpressionList f) = f return
    applyFunc (AlterSpec f) = f return
    applyFunc (AlterNothing) = return

pickFuncRep :: Monad m => FlowGraph m () -> Map.Map Meta (A.Structured -> m A.Structured)
pickFuncRep gr = Map.fromList $ map (helpApplyFunc . getMetaFunc) (labNodes gr)
  where
    getMetaFunc (_,Node (m,_,f)) = (m,f)
    
    helpApplyFunc (m,f) = (m, applyFunc (m,f))
    
    applyFunc (m,AlterProcess f) = f (g m)
    applyFunc (m,AlterExpression f) = f (g m)
    applyFunc (m,AlterExpressionList f) = f (g m)
    applyFunc (m,AlterSpec f) = f (g m)
    applyFunc (m,AlterNothing) = g m
    
    g m = everywhereM (mkM $ {-applyOnce $-} replaceM m (replaceMeta m))

-- TODO don't let the tree grow too deep (suggest 10 as maximum number of nodes that could be changed, so 2^10 powersets)
-- TODO alter the number of tests run

deepCheck p = check (defaultConfig { configMaxTest = 1000}) p

testModify :: Test
testModify = TestList
 [
   TestCase $ deepCheck prop_Id
  ,TestCase $ deepCheck prop_Rep
 ]
  where
    prop_Id :: QC (A.Structured, Map.Map [Meta] A.Structured) -> Bool
    prop_Id (QC (g,_)) = collectAll $ (flip map) (map (foldFuncsM) $ powerset $ pickFuncId $ genGraph g) $ \f -> runIdentity (f g) == g
    prop_Rep :: QC (A.Structured, Map.Map [Meta] A.Structured) -> Bool
    prop_Rep (QC (g,rest)) = collectAll $ (flip map) (helper $ pickFuncRep $ genGraph g) $ 
        \(funcs,ms) -> Just (runIdentity (applyMetas ms funcs g)) == Map.lookup ms rest

    -- Repeatedly pairs the map with each element of the powerset of its keys
    helper :: Monad m => Map.Map Meta (A.Structured -> m A.Structured) -> [(Map.Map Meta (A.Structured -> m A.Structured), [Meta])]
    helper fs = zip (repeat fs) (powerset $ Map.keys fs)

    -- Applies the functions associated with the given meta tags
    applyMetas :: Monad m => [Meta] -> Map.Map Meta (A.Structured -> m A.Structured) -> (A.Structured -> m A.Structured)
    applyMetas ms funcs = foldFuncsM $ concatMap (\m -> Map.lookup m funcs) ms


    -- Collects multiple tests together:
    collectAll = and
--    collectAll = foldl collect (property ())

--Returns the list of tests:
tests :: Test
tests = TestList
 [
  testCase
  ,testIf
  ,testModify
  ,testPar
  ,testSeq
  ,testWhile
 ]
