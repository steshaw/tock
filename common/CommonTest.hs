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

module CommonTest (tests) where

import Test.HUnit hiding (State)
import qualified AST as A
import Types
import TreeUtil
import Metadata
import Data.Generics

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

testCheckTreeForConstr :: Test
testCheckTreeForConstr = TestList
 [
   doTest (0,A.Int,[],[])
  ,doTest (1,A.Int,[tc0 A.Int],[ADI A.Int])
  ,doTest (100, A.True emptyMeta, [tc1 A.True],[ADI $ A.True emptyMeta])
  
  ,doTest (200, A.Seq emptyMeta $ A.Several emptyMeta [A.OnlyP emptyMeta $ A.Skip emptyMeta], [tc1 A.Skip], [ADI $ A.Skip emptyMeta])
  ,doTest (201, A.Seq emptyMeta $ A.Several emptyMeta [A.OnlyP emptyMeta $ A.Skip emptyMeta], [tc2 A.Several], [ADI $ A.Several emptyMeta [A.OnlyP emptyMeta $ A.Skip emptyMeta]])
  ,doTest (202, A.Seq emptyMeta $ A.Several emptyMeta [A.OnlyP emptyMeta $ A.Skip emptyMeta], [tc0 A.Int], [])
  ,doTest (203, A.Seq emptyMeta $ A.Several emptyMeta [A.OnlyP emptyMeta $ A.Skip emptyMeta], [tc2 A.OnlyP, tc1 A.Skip],
    [ADI $ A.OnlyP emptyMeta $ A.Skip emptyMeta, ADI $ A.Skip emptyMeta])
 ]
 where
   doTest :: Data a => (Int, a, [Constr], [AnyDataItem]) -> Test
   doTest (n,testIn,testFor,testOut) = TestCase $ assertEqual ("testCheckAny " ++ (show n)) testOut (checkTreeForConstr testFor testIn)
   tc0 :: Data a => a -> Constr
   tc0 = toConstr
   tc1 :: Data a => (a0 -> a) -> Constr
   tc1 f = toConstr (f undefined)
   tc2 :: Data a => (a0 -> a1 -> a) -> Constr
   tc2 f = toConstr (f undefined undefined)

--Returns the list of tests:
tests :: Test
tests = TestList
 [
   testIsSafeConversion
   ,testCheckTreeForConstr
 ]
