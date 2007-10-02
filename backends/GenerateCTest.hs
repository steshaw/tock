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
module GenerateCTest where

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
import Pattern
import TestUtil
import TreeUtil

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


testBoth :: 
  String -- ^ Test Name
  -> String -- ^ C expected
  -> String -- ^ C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> (State CompState ()) -- ^ State transformation  
  -> Test
  
testBoth testName expC expCPP act startState = TestCase $
  do assertGen (testName ++ "/C") expC $ (evalStateT (runErrorT (execWriterT $ act cgenOps)) state) 
     assertGen (testName ++ "/C++") expCPP $ (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state) 
  where
    state = execState startState emptyState

-- Tests C output, expects C++ to fail
testCF :: String -> String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testCF testName expC act startState = TestCase $
  do assertGen (testName ++ "/C") expC $ (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGenFail (testName ++ "/C++") (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState
    
-- Tests C++ output, expects C to fail
testCPPF :: String -> String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testCPPF testName expCPP act startState = TestCase $
  do assertGenFail (testName ++ "/C") (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGen (testName ++ "/C++") expCPP $ (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState    

testBothSame :: 
  String    -- ^ Test Name
  -> String -- ^ C and C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> (State CompState ()) -- ^ State transformation
  -> Test
testBothSame n e a s = testBoth n e e a s
  
tcall :: (GenOps -> GenOps -> a -> b) -> a -> (GenOps -> b)
tcall f x = (\o -> f o o x)
  
testGenType :: Test
testGenType = TestList 
 [
  testBothSame "GenType 0" "uint8_t" (tcall genType A.Byte) (return ())
  ,testBothSame "GenType 1" "uint16_t" (tcall genType A.UInt16) (return ())
  ,testBothSame "GenType 2" "uint32_t" (tcall genType A.UInt32) (return ())
  ,testBothSame "GenType 3" "uint64_t" (tcall genType A.UInt64) (return ())
  ,testBothSame "GenType 4" "int8_t" (tcall genType A.Int8) (return ())
  ,testBothSame "GenType 5" "int16_t" (tcall genType A.Int16) (return ())
  ,testBothSame "GenType 6" "int32_t" (tcall genType A.Int32) (return ())
  ,testBothSame "GenType 7" "int64_t" (tcall genType A.Int64) (return ())
  ,testBothSame "GenType 8" "int" (tcall genType A.Int) (return ())
  ,testBoth "GenType 9" "bool" "tockBool" (tcall genType A.Bool) (return ())
  ,testBothSame "GenType 10" "float" (tcall genType A.Real32) (return ())
  ,testBothSame "GenType 11" "double" (tcall genType A.Real64) (return ())
  ,testBoth "GenType 100" "int*" "tockArrayView<int,1>" (tcall genType $ A.Array [A.Dimension 5] A.Int) (return ())
  ,testBoth "GenType 101" "int*" "tockArrayView<int,3>" (tcall genType $ A.Array [A.Dimension 5, A.Dimension 2, A.Dimension 9] A.Int) (return ())
  ,testBoth "GenType 102" "int*" "tockArrayView<int,2>" (tcall genType $ A.Array [A.Dimension 5, A.UnknownDimension] A.Int) (return ())
  ,testBothSame "GenType 103" "foo" (tcall genType $ A.Record (simpleName "foo")) (return ())
  ,testBoth "GenType 200" "Time" "csp::Time" (tcall genType A.Time) (return ())
  ,testBoth "GenType 201" "Time" "csp::Time" (tcall genType A.Timer) (return ())

  ,testBoth "GenType 300" "Channel*" "csp::One2OneChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int) (return ())
  ,testBoth "GenType 301" "Channel*" "csp::One2AnyChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False True) A.Int) (return ())
  ,testBoth "GenType 302" "Channel*" "csp::Any2OneChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True False) A.Int) (return ())
  ,testBoth "GenType 303" "Channel*" "csp::Any2AnyChannel<int>*" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True True) A.Int) (return ())
  
  ,testBoth "GenType 400" "Channel*" "csp::Chanin<int>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int) (return ())
  ,testBoth "GenType 401" "Channel*" "csp::Chanin<int>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False True) A.Int) (return ())

  ,testBoth "GenType 402" "Channel*" "csp::Chanout<int>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes False False) A.Int) (return ())
  ,testBoth "GenType 403" "Channel*" "csp::Chanout<int>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes True False) A.Int) (return ())
  
  --ANY and protocols can occur outside channels in C++ (e.g. temporaries for reading from channels), so they are tested here:
  ,testCPPF "GenType 500" "tockAny" (tcall genType $ A.Any) (return ())
  ,testCPPF "GenType 600" "protocol_foo" (tcall genType $ A.UserProtocol (simpleName "foo")) (return ())
 ]

---Returns the list of tests:
tests :: Test
tests = TestList
 [
   testGenType
 ]


