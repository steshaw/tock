{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

module CheckTest (tests) where

import Test.HUnit

import qualified AST as A
import Check
import CheckFramework
import Metadata
import OccamEDSL
import TestUtils

testUnusedVar :: Test
testUnusedVar = TestList
 [
   testSame "No variables" $ wrap $ oSEQ []
  ,testSame "One used variable" $ wrap $
    oSEQ [
      decl (return A.Int) oX
        [oX *:= (return (0::Int))]
    ]
  ,testWarn 1 "One unused variable" $ wrap $
    oSEQ [
      decl (return A.Int) oX []
    ]
    `becomes` oSEQ []

  ,testWarn 3 "Three unused variables" $ wrap $
    oSEQ [
      decl (return A.Int) oX [decl (return A.Int) oY [decl (return A.Int) oZ []]]
    ]
    `becomes` oSEQ []

  ,testWarn 1 "Unused variable in loop" $ wrap $
    oWHILE True $
      oSEQ
        [decl (return A.Int) oX []]
      `becomes`
      oSEQ []
 ]
 where
   wrap x = oPROC "foo" [] x oempty

   testSame :: String -> Occ A.AST -> Test
   testSame name x = testOccamPassWarn ("checkUnusedVar " ++ name) null x
     (runChecksPass checkUnusedVar)
   testWarn :: Int -> String -> Occ A.AST -> Test
   testWarn n name x = testOccamPassWarn ("checkUnusedVar " ++ name) ((== n) . length) x
     (runChecksPass checkUnusedVar)

tests :: Test
tests = TestLabel "CheckTest" $ TestList
 [
  testUnusedVar
 ]


