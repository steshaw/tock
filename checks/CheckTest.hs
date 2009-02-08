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

module CheckTest (viotests) where

import Control.Monad
import Test.HUnit

import qualified AST as A
import Check
import CheckFramework
import CompState
import Metadata
import OccamEDSL
import TestHarness
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

  ,testSame "Used array variable" $ wrap $
    oSEQ [
      decl (return $ A.Array [A.Dimension $ intLiteral 2] A.Int) oX
        [oX `sub` 0 *:= (return (0::Int))]
    ]

  ,testSame "One variable, used in one IF branch" $ wrap $
    oSEQ [
      decl (return A.Int) oX
        [oIF
          [ifChoice (True, oX *:= (return (0::Int)))
          ,ifChoice (True, oSKIP)
          ]
        ]
    ]
  ,testSame "One variable, declared in an IF and used in one IF branch" $ wrap $
       oIF
       [
         decl (return A.Int) oX       
          [ifChoice (True, oX *:= (return (0::Int)))
          ,ifChoice (True, oSKIP)
          ]
       ]
  ,testSame "One variable, declared in an IF and used in second IF branch" $ wrap $
       oIF
       [
         decl (return A.Int) oX       
          [ifChoice (True, oSKIP)
          ,ifChoice (True, oX *:= (return (0::Int)))
          ]
       ]

 ]
 where
   wrap x = oPROC "foo" [] x oempty

   testSame :: String -> Occ A.AST -> Test
   testSame name x = testOccamPassWarn ("checkUnusedVar " ++ name) null x
     (runChecksPass checkUnusedVar)
   testWarn :: Int -> String -> Occ A.AST -> Test
   testWarn n name x = testOccamPassWarn ("checkUnusedVar " ++ name) ((== n) . length) x
     (runChecksPass checkUnusedVar)

viotests :: Int -> IO Test
viotests v = liftM (TestLabel "CheckTest" . TestList) $ sequence
 [
  return testUnusedVar
 ,automaticTest FrontendOccam v "testcases/automatic/abbrev-check-1.occ.test"
 ]


