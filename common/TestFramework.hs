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

-- | A unified test framework that allows tests to be used in either
-- HUnit, QuickCheck (or any future test frameworks).
module TestFramework where

import Control.Monad.Error
import Data.Generics
import Test.HUnit hiding (Testable)
import Test.QuickCheck hiding (check)

import PrettyShow

instance Error Result where
  noMsg = strMsg ""
  strMsg s = Result (Just False) [s] []

class Monad m => TestMonad m r | m -> r where
  runTest :: m () -> r
  testFailure :: String -> m ()

instance TestMonad IO Assertion where
  runTest = id
  testFailure = assertFailure
  
instance TestMonad (Either Result) Result where
  runTest = either id (const $ Result (Just True) [] [])
  testFailure s = Left $ Result (Just False) [] [s]

compareForResult :: TestMonad m r => String -> (a -> String) -> (a -> a -> Bool) -> a -> a -> m ()
compareForResult msg showFunc cmpFunc exp act
  | cmpFunc exp act = return ()
  | otherwise = testFailure (msg ++ "\n" ++ "expected: " ++ showFunc exp ++ "\n but got: " ++ showFunc act)

-- | An equality operator for comparing expected (LHS) to actual (RHS) 
(*==*) :: (Data a, Eq a, TestMonad m r) => a -> a -> m ()
(*==*) = compareForResult "" pshow (==)

(*&&*) :: TestMonad m r => m () -> m () -> m ()
(*&&*) = (>>)

type QCProp = Either Result ()

-- | A type-constrained version of runTest for QuickCheck Testable things:
runQCTest :: QCProp -> Result
runQCTest = runTest

testEqual :: (Show a, Eq a, TestMonad m r) => String -> a -> a -> m ()
testEqual msg = compareForResult msg show (==)

testEqualCustomShow :: (Eq a, TestMonad m r) => (a -> String) -> String -> a -> a -> m ()
testEqualCustomShow showFunc testName = compareForResult testName showFunc (==)

testCompareCustom :: 
  (Show a, TestMonad m r) => 
  String               -- ^ The message\/test name to prefix on failure.
  -> (a -> a -> Bool)  -- ^ The comparison function.  A return of True means the Assertion will succeed, False means the Assertion will fail.
  -> a                 -- ^ The expected\/yardstick value.
  -> a                 -- ^ The actual value from running the test.
  -> m ()
testCompareCustom testName = compareForResult testName show
