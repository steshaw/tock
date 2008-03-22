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

-- #ignore-exports

-- | Tests for 'OccamTypes'.
module OccamTypesTest (tests) where

import Control.Monad.State
import Data.Generics
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Metadata
import qualified OccamTypes
import TestUtils

m :: Meta
m = emptyMeta

-- | Initial state for the tests.
startState :: State CompState ()
startState
    =  do defineConst "constInt" A.Int (intLiteral 2)
          defineConst "constInts" intsT (A.Literal m intsT arrayLit)
          defineVariable "varInt" A.Int
          defineVariable "varByte" A.Byte
          defineVariable "varReal" A.Real32
          defineVariable "varInts" (A.Array [A.UnknownDimension] A.Int)
          defineVariable "varBytes" (A.Array [A.UnknownDimension] A.Byte)
          defineUserDataType "MYINT" A.Int
          defineUserDataType "MY2INT" (A.Array [dimension 2] A.Int)
          defineRecordType "COORD2" [("x", A.Int), ("y", A.Int)]
          defineRecordType "COORD3" [("x", A.Real32), ("y", A.Real32),
                                     ("z", A.Real32)]
          defineChannel "chanInt" chanIntT
          defineChannel "chansInt" (A.Array [A.UnknownDimension] chanIntT)
          defineVariable "mobileInt" (A.Mobile A.Int)
          defineFunction "function0" [A.Int] []
          defineFunction "function1" [A.Int] [("x", A.Int)]
          defineFunction "function2" [A.Int] [("x", A.Int), ("y", A.Int)]
          defineFunction "function22" [A.Int, A.Int]
                                      [("x", A.Int), ("y", A.Int)]
  where
    ca = A.ChanAttributes False False
    intsT = A.Array [A.UnknownDimension] A.Int
    arrayLit = A.ArrayLiteral m []
    chanIntT = A.Chan A.DirUnknown ca A.Int

-- | Test the typechecker.
testOccamTypes :: Test
testOccamTypes = TestList
    [
    -- Subscript expressions
      testOK     0 $ A.Subscript m A.NoCheck intE
    , testFail   1 $ A.Subscript m A.NoCheck byteE
    , testOK     2 $ A.SubscriptFromFor m intE intE
    , testFail   3 $ A.SubscriptFromFor m byteE byteE
    , testOK     4 $ A.SubscriptFrom m intE
    , testFail   5 $ A.SubscriptFrom m byteE
    , testOK     6 $ A.SubscriptFor m intE
    , testFail   7 $ A.SubscriptFor m byteE

    -- Trivial literals
    , testOK    20 $ intE
    , testOK    21 $ byteE

    -- Array literals
    , testOK    30 $ A.Literal m twoIntsT twoInts
    , testFail  31 $ A.Literal m threeIntsT twoInts
    , testFail  32 $ A.Literal m twoBytesT twoInts
    , testFail  33 $ A.Literal m A.Int twoInts
    , testFail  34 $ A.Literal m twoTwoIntsT twoInts
    , testOK    35 $ A.Literal m myTwoIntsT twoInts
    , testFail  36 $ A.Literal m myIntT twoInts

    -- Record literals
    , testFail  40 $ A.Literal m coord2T twoInts
    , testOK    41 $ A.Literal m coord2T coord2
    , testFail  42 $ A.Literal m coord2T coord3
    , testOK    43 $ A.Literal m coord3T coord3
    , testFail  44 $ A.Literal m coord3T coord2
    , testFail  45 $ A.Literal m A.Int coord2
    , testFail  46 $ A.Literal m twoIntsT coord2
    , testFail  47 $ A.Literal m myTwoIntsT coord2

    -- Variables
    , testOK    50 $ intV
    , testOK    51 $ bytesV
    , testOK    52 $ A.DirectedVariable m A.DirInput chanIntV
    , testFail  53 $ A.DirectedVariable m A.DirInput intV
    , testOK    54 $ A.DerefVariable m mobileIntV
    , testFail  55 $ A.DerefVariable m chanIntV

    -- Operators in expressions
    , testOK   100 $ A.Monadic m A.MonadicSubtr intE
    , testFail 101 $ A.Monadic m A.MonadicSubtr twoIntsE
    , testFail 102 $ A.Monadic m A.MonadicSubtr boolE
    , testFail 103 $ A.Monadic m A.MonadicNot intE
    , testOK   104 $ A.Monadic m A.MonadicNot boolE
    , testOK   105 $ A.Dyadic m A.Add intE intE
    , testFail 106 $ A.Dyadic m A.Add intE byteE
    , testFail 107 $ A.Dyadic m A.Add byteE intE
    , testFail 108 $ A.Dyadic m A.Add byteE boolE
    , testOK   109 $ A.Dyadic m A.LeftShift intE intE
    , testOK   110 $ A.Dyadic m A.LeftShift byteE intE
    , testFail 111 $ A.Dyadic m A.LeftShift intE byteE
    , testOK   112 $ A.Dyadic m A.And boolE boolE
    , testFail 113 $ A.Dyadic m A.And boolE intE
    , testFail 114 $ A.Dyadic m A.And intE boolE
    , testFail 115 $ A.Dyadic m A.Add twoIntsE twoIntsE
    , testOK   116 $ A.Dyadic m A.Concat listE listE
    , testFail 117 $ A.Dyadic m A.Concat listE intE
    , testFail 118 $ A.Dyadic m A.Concat intE listE

    -- Miscellaneous expressions
    , testOK   150 $ A.MostPos m A.Int
    , testFail 151 $ A.MostPos m twoIntsT
    , testOK   152 $ A.MostNeg m A.Int
    , testFail 153 $ A.MostNeg m twoIntsT
    , testOK   154 $ A.SizeType m twoIntsT
    , testFail 155 $ A.SizeType m A.Int
    , testOK   156 $ A.SizeExpr m twoIntsE
    , testFail 157 $ A.SizeExpr m intE
    , testOK   158 $ A.SizeExpr m twoTwoIntsE
    , testOK   159 $ A.SizeExpr m (sub0E twoTwoIntsE)
    , testFail 160 $ A.SizeExpr m (sub0E (sub0E twoTwoIntsE))
    , testFail 161 $ A.SizeExpr m (sub0E intE)
    , testOK   162 $ A.SizeVariable m intsV
    , testFail 163 $ A.SizeVariable m byteV
    , testOK   164 $ A.ExprVariable m intV
    , testOK   165 $ intE
    , testOK   166 $ boolLiteral True
    , testOK   167 $ A.IntrinsicFunctionCall m "SQRT" [realE]
    , testFail 168 $ A.IntrinsicFunctionCall m "SQRT" [intE]
    , testFail 169 $ A.IntrinsicFunctionCall m "SQRT" [realE, intE]
    , testOK   170 $ subxE coord2E
    , testFail 171 $ subxE twoTwoIntsE
    , testFail 172 $ subxE intE
    , testFail 173 $ A.SubscriptedExpr m (A.SubscriptField m function0) coord2E
    , testOK   174 $ A.OffsetOf m coord2T (simpleName "x")
    , testFail 175 $ A.OffsetOf m coord2T function0
    , testFail 176 $ A.OffsetOf m A.Int (simpleName "x")

    -- Conversions
    , testOK   200 $ A.Conversion m A.Round A.Int realE
    , testOK   201 $ A.Conversion m A.Round A.Real32 intE
    , testFail 202 $ A.Conversion m A.Round A.Real32 twoIntsE
    , testFail 203 $ A.Conversion m A.Round twoIntsT realE

    -- Function calls
    , testOK   220 $ A.FunctionCall m function0 []
    , testOK   221 $ A.FunctionCall m function1 [intE]
    , testOK   222 $ A.FunctionCall m function2 [intE, intE]
    , testFail 223 $ A.FunctionCall m function22 [intE, intE]
    , testFail 224 $ A.FunctionCall m function0 [intE]
    , testFail 225 $ A.FunctionCall m function1 [intE, intE]
    , testFail 226 $ A.FunctionCall m function2 [intE]
    , testFail 227 $ A.FunctionCall m function2 [intE, intE, intE]
    , testFail 228 $ A.FunctionCall m (simpleName "someInt") [intE]
    , testFail 229 $ A.FunctionCall m function1 [realE]
    , testFail 230 $ A.FunctionCall m function2 [intE, realE]
    , testFail 231 $ A.FunctionCall m function2 [twoIntsE, intE]
    , testOK   232 $ A.FunctionCall m function1 [sub0E twoIntsE]

    -- Mobile allocations
    , testOK   250 $ A.AllocMobile m (A.Mobile A.Int) (Just intE)
    , testOK   251 $ A.AllocMobile m (A.Mobile A.Int) Nothing
    , testFail 252 $ A.AllocMobile m (A.Mobile A.Int) (Just realE)
    , testFail 253 $ A.AllocMobile m (A.Mobile A.Int) (Just realE)
    , testOK   254 $ A.AllocMobile m (A.Mobile A.Real32) (Just realE)
    , testOK   254 $ A.AllocMobile m (A.Mobile twoIntsT) (Just twoIntsE)
    , testFail 255 $ A.AllocMobile m (A.Mobile unknownIntsT) (Just twoIntsE)
    , testFail 256 $ A.AllocMobile m (A.Mobile unknownIntsT) Nothing

    -- Input items
    , testOK   300 $ A.InCounted m intV intsV
    , testFail 301 $ A.InCounted m realV intsV
    , testFail 302 $ A.InCounted m intV intV
    , testFail 303 $ A.InCounted m constIntV intsV
    , testFail 304 $ A.InCounted m intV constIntsV
    , testFail 305 $ A.InCounted m intV chansIntV
    , testOK   306 $ A.InVariable m intV
    , testFail 307 $ A.InVariable m constIntV
    , testFail 308 $ A.InVariable m chanIntV

    -- Output items
    , testOK   310 $ A.OutCounted m intE twoIntsE
    , testFail 311 $ A.OutCounted m realE twoIntsE
    , testFail 312 $ A.OutCounted m intE intE
    , testOK   313 $ A.OutExpression m intE
    , testFail 313 $ A.OutExpression m chanIntE

    -- Replicators
    , testOK   320 $ A.For m i intE intE
    , testFail 321 $ A.For m i realE intE
    , testFail 322 $ A.For m i intE realE
    , testOK   323 $ A.ForEach m i twoIntsE
    , testOK   324 $ A.ForEach m i listE
    , testFail 324 $ A.ForEach m i intE

    -- Choices
    , testOK   330 $ A.Choice m boolE skip
    , testFail 331 $ A.Choice m intE skip
    ]
  where
    testOK :: (Show a, Data a) => Int -> a -> Test
    testOK n orig
        = TestCase $ testPass ("testOccamTypes" ++ show n)
                              orig (OccamTypes.checkTypes orig)
                              startState

    testFail :: (Show a, Data a) => Int -> a -> Test
    testFail n orig
        = TestCase $ testPassShouldFail ("testOccamTypes" ++ show n)
                                        (OccamTypes.checkTypes orig)
                                        startState

    intV = variable "varInt"
    intE = intLiteral 42
    realV = variable "varReal"
    realE = A.Literal m A.Real32 $ A.RealLiteral m "3.14159"
    byteV = variable "varByte"
    byteE = byteLiteral 42
    intsV = variable "varInts"
    bytesV = variable "varBytes"
    constIntV = variable "constInt"
    constIntsV = variable "constInts"
    boolE = boolLiteral True
    unknownIntsT = A.Array [A.UnknownDimension] A.Int
    twoIntsT = A.Array [dimension 2] A.Int
    twoTwoIntsT = A.Array [dimension 2, dimension 2] A.Int
    twoBytesT = A.Array [dimension 2] A.Byte
    threeIntsT = A.Array [dimension 3] A.Int
    ae = A.ArrayElemExpr intE
    twoInts = A.ArrayLiteral m [ae, ae]
    twoIntsE = A.Literal m twoIntsT twoInts
    twoTwoInts = A.ArrayLiteral m [A.ArrayElemArray [ae, ae],
                                   A.ArrayElemArray [ae, ae]]
    twoTwoIntsE = A.Literal m twoTwoIntsT twoTwoInts
    myIntT = A.UserDataType (simpleName "MYINT")
    myTwoIntsT = A.UserDataType (simpleName "MY2INT")
    coord2T = A.Record (simpleName "COORD2")
    coord2 = A.RecordLiteral m [intE, intE]
    coord2E = A.Literal m coord2T coord2
    coord3T = A.Record (simpleName "COORD3")
    coord3 = A.RecordLiteral m [realE, realE, realE]
    chanIntV = variable "chanInt"
    chanIntE = A.ExprVariable m chanIntV
    chansIntV = variable "chanInt"
    mobileIntV = variable "mobileInt"
    sub0 = A.Subscript m A.NoCheck (intLiteral 0)
    sub0E = A.SubscriptedExpr m sub0
    subx = A.SubscriptField m (simpleName "x")
    subxE = A.SubscriptedExpr m subx
    function0 = simpleName "function0"
    function1 = simpleName "function1"
    function2 = simpleName "function2"
    function22 = simpleName "function22"
    listT = A.List A.Int
    listE = A.Literal m listT (A.ListLiteral m [intE, intE, intE])
    i = simpleName "i"
    skip = A.Skip m

tests :: Test
tests = TestLabel "OccamTypesTest" $ TestList
    [ testOccamTypes
    ]
