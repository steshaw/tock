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

-- | A module with tests for various miscellaneous things in the common directory.
module CommonTest (tests) where

import Data.Generics
import Test.HUnit hiding (State)

import qualified AST as A
import Metadata
import TreeUtils
import Types

-- | Tests the isSafeConversion function:
testIsSafeConversion :: Test
testIsSafeConversion = TestList $ map runTestRow resultsWithIndexes
  where
    resultsWithIndexes :: [(Int,[(Int,Bool)])]
    resultsWithIndexes = zip [0..] $ map (zip [0..]) results
    
    runTestRow :: (Int,[(Int,Bool)]) -> Test
    runTestRow (a,b) = TestList $ map (runTest a) b
      where
        runTest :: Int -> (Int,Bool) -> Test
        runTest destIndex (srcIndex,result) = TestCase $ assertEqual 
          ("Testing from type: " ++ (show $ index srcIndex) ++ " to: " ++ (show $ index destIndex))
          result $ isSafeConversion (index srcIndex) (index destIndex)
      
--Integer types are:
--A.Bool
--A.Byte
--A.UInt16
--A.UInt32
--A.UInt64
--A.Int8
--A.Int
--A.Int16
--A.Int32
--A.Int64

--We will assume (like the rest of Tock) that Int is 32-bits for testing.  We can actually perform an exhaustive test without too much trouble:
    index :: Int -> A.Type
    index 0 = A.Bool
    index 1 = A.Byte
    index 2 = A.UInt16
    index 3 = A.UInt32
    index 4 = A.UInt64
    index 5 = A.Int8
    index 6 = A.Int16
    index 7 = A.Int
    index 8 = A.Int32
    index 9 = A.Int64

    t = True
    f = False

    results :: [[Bool]]
    --Each row is a conversion to that type.  For example, the first row is conversions *to* Bool:
    results =
      [ [t, f,f,f,f, f,f,f,f,f] --to Bool

       ,[t, t,f,f,f, f,f,f,f,f] --to Byte
       ,[t, t,t,f,f, f,f,f,f,f] --to UInt16
       ,[t, t,t,t,f, f,f,f,f,f] --to UInt32
       ,[t, t,t,t,t, f,f,f,f,f] --to UInt64

       ,[t, f,f,f,f, t,f,f,f,f] --to Int8
       ,[t, t,f,f,f, t,t,f,f,f] --to Int16
       ,[t, t,t,f,f, t,t,t,t,f] --to Int
       ,[t, t,t,f,f, t,t,t,t,f] --to Int32
       ,[t, t,t,t,f, t,t,t,t,t] --to Int64
      ]

-- | Tests the pass that checks a certain constructor is not present in the tree.
-- Here, we provide various small AST fragments, and check that the list of constructors returned
-- is the same as we expected.
testCheckTreeForConstr :: Test
testCheckTreeForConstr = TestList
 [
   doTest (0,A.Int,[],[])
  ,doTest (1,A.Int,[con0 A.Int],[ADI A.Int])
  ,doTest (100, A.True emptyMeta, [con1 A.True],[ADI $ A.True emptyMeta])
  
  ,doTest (200, A.Seq emptyMeta $ A.Several emptyMeta [A.Only emptyMeta $ A.Skip emptyMeta], [con1 A.Skip], [ADI $ A.Skip emptyMeta])
  ,doTest (201, A.Seq emptyMeta $ A.Several emptyMeta [A.Only emptyMeta $ A.Skip emptyMeta],
    [con2 (A.Several :: Meta -> [A.Structured A.Process] -> A.Structured A.Process)],
    [ADI $ A.Several emptyMeta [A.Only emptyMeta $ A.Skip emptyMeta]])
  ,doTest (202, A.Seq emptyMeta $ A.Several emptyMeta [A.Only emptyMeta $ A.Skip emptyMeta], [con0 A.Int], [])
  ,doTest (203, A.Seq emptyMeta $ A.Several emptyMeta [A.Only emptyMeta $ A.Skip emptyMeta], [con2 (A.Only :: Meta -> A.Process -> A.Structured A.Process), con1 A.Skip],
    [ADI $ A.Only emptyMeta $ A.Skip emptyMeta, ADI $ A.Skip emptyMeta])
 ]
 where
   doTest :: Data a => (Int, a, [Constr], [AnyDataItem]) -> Test
   doTest (n,testIn,testFor,testOut) = TestCase $ assertEqual ("testCheckAny " ++ (show n)) testOut (checkTreeForConstr testFor testIn)

testDecomp :: Test
testDecomp = TestList
 [
   doTest 0 (Just $ Just "xy") (decomp1 Just (return . (++ "y")) (Just "x"))
  ,doTest 1 Nothing (decomp1 Right (return . (++ "y")) (Left "x"))
 ]
 where
   doTest :: (Eq a, Show a) => Int -> Maybe a -> Maybe a -> Test
   doTest n exp act = TestCase $ assertEqual ("testDecomp " ++ show n) exp act


--Returns the list of tests:
tests :: Test
tests = TestLabel "CommonTest" $ TestList
 [
   testIsSafeConversion
   ,testCheckTreeForConstr
   ,testDecomp
 ]
