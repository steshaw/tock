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

-- | Tests for the C and C++ backends
module GenerateCTest (tests) where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Writer
import Data.List (isInfixOf)
import Test.HUnit hiding (State)
import Text.Regex

import qualified AST as A
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import Metadata
import Pattern
import TestUtil
import TreeUtil

at :: CGen ()
at = tell ["@"]

dollar :: CGen ()
dollar = tell ["$"]

foo :: A.Name
foo = simpleName "foo"

-- | Asserts that the given output of a CGen pass matches the expected value.
assertGen :: String -> String -> IO (Either Errors.ErrorReport [String]) -> Assertion
assertGen n exp act
      = do r <- act 
           case r of 
             Left (_,err) -> assertFailure $ n ++ " pass failed, error: " ++ err
             Right ss -> assertEqual n exp (subRegex (mkRegex "/\\*\\*/") (concat ss) "")


-- | Asserts that the given output of a CGen pass is a failure
assertGenFail :: String -> IO (Either Errors.ErrorReport [String]) -> Assertion
assertGenFail n act
      = do r <- act 
           case r of 
             Left _ -> return ()
             Right ss -> if isInfixOf "#error" (concat ss)
                           then return ()
                           else assertFailure $ n ++ " pass succeeded when expected to fail, output: " ++ (subRegex (mkRegex "/\\*\\*/") (concat ss) "")


testBothS :: 
  String -- ^ Test Name
  -> String -- ^ C expected
  -> String -- ^ C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> (State CompState ()) -- ^ State transformation  
  -> Test
  
testBothS testName expC expCPP act startState = TestCase $
  do assertGen (testName ++ "/C") expC $ (evalStateT (runErrorT (execWriterT $ act cgenOps)) state) 
     assertGen (testName ++ "/C++") expCPP $ (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state) 
  where
    state = execState startState emptyState

testBothFailS :: String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testBothFailS testName act startState = TestCase $
  do assertGenFail (testName ++ "/C") (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGenFail (testName ++ "/C++") (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState

-- Tests C output, expects C++ to fail
testCFS :: String -> String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testCFS testName expC act startState = TestCase $
  do assertGen (testName ++ "/C") expC $ (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGenFail (testName ++ "/C++") (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState
    
-- Tests C++ output, expects C to fail
testCPPFS :: String -> String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testCPPFS testName expCPP act startState = TestCase $
  do assertGenFail (testName ++ "/C") (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGen (testName ++ "/C++") expCPP $ (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState    

testBothSameS :: 
  String    -- ^ Test Name
  -> String -- ^ C and C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> (State CompState ()) -- ^ State transformation
  -> Test
testBothSameS n e a s = testBothS n e e a s

testBothFail :: String -> (GenOps -> CGen ()) -> Test
testBothFail a b = testBothFailS a b (return ())
  
testBoth :: String -> String -> String -> (GenOps -> CGen ()) -> Test
testBoth a b c d = testBothS a b c d (return ())

testBothSame :: String -> String -> (GenOps -> CGen ()) -> Test
testBothSame a b c = testBothSameS a b c (return ())
  
testCF :: String -> String -> (GenOps -> CGen ()) -> Test
testCF a b c = testCFS a b c (return ())

testCPPF :: String -> String -> (GenOps -> CGen ()) -> Test
testCPPF a b c = testCPPFS a b c (return ())
  
tcall :: (GenOps -> GenOps -> a -> b) -> a -> (GenOps -> b)
tcall f x = (\o -> f o o x)

tcall2 :: (GenOps -> GenOps -> a0 -> a1 -> b) -> a0 -> a1 -> (GenOps -> b)
tcall2 f x y = (\o -> f o o x y)

tcall3 :: (GenOps -> GenOps -> a0 -> a1 -> a2 -> b) -> a0 -> a1 -> a2 -> (GenOps -> b)
tcall3 f x y z = (\o -> f o o x y z)

-- | Overrides a specified function in GenOps to return the given value
override1 ::
  b -- ^ The value to return for the overridden function
  -> (GenOps -> a -> b) -- ^ The resulting overriden function
override1 val = (\_ _ -> val)

testGenType :: Test
testGenType = TestList 
 [
  testBothSame "GenType 0" "uint8_t" (tcall genType A.Byte) 
  ,testBothSame "GenType 1" "uint16_t" (tcall genType A.UInt16) 
  ,testBothSame "GenType 2" "uint32_t" (tcall genType A.UInt32) 
  ,testBothSame "GenType 3" "uint64_t" (tcall genType A.UInt64) 
  ,testBothSame "GenType 4" "int8_t" (tcall genType A.Int8) 
  ,testBothSame "GenType 5" "int16_t" (tcall genType A.Int16) 
  ,testBothSame "GenType 6" "int32_t" (tcall genType A.Int32) 
  ,testBothSame "GenType 7" "int64_t" (tcall genType A.Int64) 
  ,testBothSame "GenType 8" "int" (tcall genType A.Int) 
  ,testBoth "GenType 9" "bool" "tockBool" (tcall genType A.Bool) 
  ,testBothSame "GenType 10" "float" (tcall genType A.Real32) 
  ,testBothSame "GenType 11" "double" (tcall genType A.Real64) 
  ,testBoth "GenType 100" "int*" "tockArrayView<int,1>" (tcall genType $ A.Array [A.Dimension 5] A.Int) 
  ,testBoth "GenType 101" "int*" "tockArrayView<int,3>" (tcall genType $ A.Array [A.Dimension 5, A.Dimension 2, A.Dimension 9] A.Int) 
  ,testBoth "GenType 102" "int*" "tockArrayView<int,2>" (tcall genType $ A.Array [A.Dimension 5, A.UnknownDimension] A.Int) 
  ,testBothSame "GenType 103" "foo" (tcall genType $ A.Record (simpleName "foo")) 
  ,testBoth "GenType 200" "Time" "csp::Time" (tcall genType A.Time) 
  ,testBoth "GenType 201" "Time" "csp::Time" (tcall genType A.Timer) 

  ,testBoth "GenType 300" "Channel*" "csp::One2OneChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int) 
  ,testBoth "GenType 301" "Channel*" "csp::One2AnyChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False True) A.Int) 
  ,testBoth "GenType 302" "Channel*" "csp::Any2OneChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True False) A.Int) 
  ,testBoth "GenType 303" "Channel*" "csp::Any2AnyChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True True) A.Int) 
  
  ,testBoth "GenType 400" "Channel*" "csp::Chanin<int>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int) 
  ,testBoth "GenType 401" "Channel*" "csp::Chanin<int>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False True) A.Int) 

  ,testBoth "GenType 402" "Channel*" "csp::Chanout<int>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes False False) A.Int) 
  ,testBoth "GenType 403" "Channel*" "csp::Chanout<int>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes True False) A.Int) 
  
  --ANY and protocols can occur outside channels in C++ (e.g. temporaries for reading from channels), so they are tested here:
  ,testCPPF "GenType 500" "tockAny" (tcall genType $ A.Any) 
  ,testCPPF "GenType 600" "protocol_foo" (tcall genType $ A.UserProtocol (simpleName "foo")) 
 ]

testStop :: Test
testStop =
  testBoth "Stop" "occam_stop(\"foo:4:9\",\"bar\");" "throw StopException(\"foo:4:9\" \"bar\");" (tcall2 genStop (Meta (Just "foo") 4 9) "bar") 

testArraySizes :: Test
testArraySizes = TestList
 [
  testBothSame "genArraySizesLiteral 0" "3" (tcall genArraySizesLiteral [A.Dimension 3]) 
  ,testBothSame "genArraySizesLiteral 1" "3,6,8" (tcall genArraySizesLiteral [A.Dimension 3, A.Dimension 6, A.Dimension 8]) 
  ,testBothFail "genArraySizesLiteral 2" (tcall genArraySizesLiteral [A.Dimension 6, A.UnknownDimension]) 
  ,testBothSame "genArraySizesSize 0" "[1]" (tcall genArraySizesSize [A.Dimension 7])
  ,testBothSame "genArraySize 0" "const int*foo_sizes=@;" (tcall3 genArraySize True at foo)
  ,testBothSame "genArraySize 1" "const int foo_sizes[]={@};" (tcall3 genArraySize False at foo)
  ,testBothSame "genArrayLiteralElems 0" "$" $ (tcall genArrayLiteralElems [A.ArrayElemExpr undefined]) . unfolded
  ,testBothSame "genArrayLiteralElems 1" "$,$,$" $ (tcall genArrayLiteralElems [A.ArrayElemExpr undefined, A.ArrayElemExpr undefined, A.ArrayElemExpr undefined]) . unfolded
  ,testBothSame "genArrayLiteralElems 2" "$,$,$" $ (tcall genArrayLiteralElems [A.ArrayElemExpr undefined, A.ArrayElemArray [A.ArrayElemExpr undefined, A.ArrayElemExpr undefined]]) . unfolded
 ]
 where
  unfolded = (\ops -> ops {genUnfoldedExpression = override1 dollar})

testActuals :: Test
testActuals = TestList
 [
  -- C adds a prefix comma (to follow Process* me) but C++ does not:
  testBoth "genActuals 0" ",@,@" "@,@" $ (tcall genActuals [undefined, undefined]) . (\ops -> ops {genActual = override1 at})
  ,testBothSame "genActuals 1" "" $ (tcall genActuals [])
  
  --For expressions, genExpression should be called:
  ,testBothSame "genActual 0" "$" $ (tcall genActual $ A.ActualExpression A.Bool (A.True undefined)) . over
  
  --For abbreviating arrays, C++ should call genExpression/genVariable, whereas C should do its foo,foo_sizes thing:
  ,testBoth "genActual 1" "@,@_sizes" "$" $ (tcall genActual $ A.ActualExpression (A.Array undefined undefined) (A.ExprVariable undefined $ A.Variable undefined foo)) . over
  ,testBoth "genActual 2" "@,@_sizes" "@" $ (tcall genActual $ A.ActualVariable A.Abbrev (A.Array undefined undefined) (A.Variable undefined foo)) . over
 ]
 where
   over = (\ops -> ops {genVariable = override1 at, genExpression = override1 dollar})

---Returns the list of tests:
tests :: Test
tests = TestList
 [
   testActuals
   ,testArraySizes
   ,testGenType
   ,testStop
 ]
