{-
Tock: a compiler for parallel languages
Copyright (C) 2008, 2009  University of Kent

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

-- | Tests for 'SimplifyAbbrevs'.
module SimplifyAbbrevsTest (tests) where

import Control.Monad.State
import Data.Generics (Data)
import Test.HUnit hiding (State)

import CompState
import qualified AST as A
import Metadata
import Pattern
import SimplifyAbbrevs
import TagAST
import TestUtils
import Traversal
import TreeUtils

m :: Meta
m = emptyMeta

setupState :: State CompState ()
setupState
    = return ()

testRemoveInitial :: Test
testRemoveInitial = TestLabel "testRemoveInitial" $ TestList
  [ -- Nothing to do
    ok    0 inner
            inner

    -- INITIAL abbreviation
  , ok   10 (spec foo (A.Is m A.InitialAbbrev A.Int $ A.ActualExpression exp)
              inner)
            (mDeclareAssign foo A.Int exp inner)

    -- INITIAL retyping
  , ok   20 (spec foo (A.RetypesExpr m A.InitialAbbrev A.Int exp)
              inner)
            (mSpec mTemp (A.RetypesExpr m A.InitialAbbrev A.Int exp)
              (mDeclareAssign foo A.Int mTempE inner))

    -- INITIAL formal
  , ok   30 (spec foo (A.Proc m
                              (A.PlainSpec, A.PlainRec)
                              [A.Formal A.InitialAbbrev A.Int bar]
                              $ Just skip)
              inner)
            (mSpec foo (mProc (A.PlainSpec, A.PlainRec)
                              [mFormal' A.ValAbbrev A.Int mTemp]
                              (Just $ mSeq
                                (mDeclareAssign bar A.Int mTempE
                                  (A.Only m skip))))
              inner)

    -- Two INITIAL formals and a regular VAL formal
  , ok   40 (spec foo (A.Proc m
                              (A.PlainSpec, A.PlainRec)
                              [ A.Formal A.InitialAbbrev A.Int bar
                              , A.Formal A.ValAbbrev     A.Int baz
                              , A.Formal A.InitialAbbrev A.Int quux
                              ]
                              (Just skip))
              inner)
            (mSpec foo (mProc (A.PlainSpec, A.PlainRec)
                              [ mFormal' A.ValAbbrev A.Int mTemp
                              , mFormal' A.ValAbbrev A.Int baz
                              , mFormal' A.ValAbbrev A.Int mTemp2
                              ]
                              (Just $ mSeq
                                (mDeclareAssign bar A.Int mTempE
                                  (mOnlyP
                                    (mSeq
                                      (mDeclareAssign quux A.Int mTempE2
                                        (A.Only m skip)))))))
              inner)
  ]
  where
    ok :: (AlloyA a (ExtOpMS BaseOpM) BaseOpM
          ,AlloyA a BaseOpM (ExtOpMS BaseOpM)
          ,Data a, Data b) => Int -> a -> b -> Test
    ok n inp exp = TestCase $ testPass ("testRemoveInitial" ++ show n)
                                       exp removeInitial inp setupState

    skip = A.Skip m
    inner = A.Only m skip
    spec n st s = A.Spec m (A.Specification m n st) s
    mSpec :: (Data a, Data b, Data c) => a -> b -> c -> Pattern
    mSpec n st s = mSpecP (tag3 A.Specification m n st) s
    foo = simpleName "foo"
    bar = simpleName "bar"
    barV = A.Variable m bar
    baz = simpleName "baz"
    quux = simpleName "quux"
    exp = A.ExprVariable m barV
    mTemp :: Pattern
    mTemp = Named "temp" DontCare
    mTempV :: Pattern
    mTempV = mVariable mTemp
    mTempE :: Pattern
    mTempE = mExprVariable mTempV
    mTemp2 :: Pattern
    mTemp2 = Named "temp2" DontCare
    mTempV2 :: Pattern
    mTempV2 = mVariable mTemp2
    mTempE2 :: Pattern
    mTempE2 = mExprVariable mTempV2
    mAssign :: (Data a, Data b) => a -> b -> Pattern
    mAssign v e = tag3 A.Assign m [v] (tag2 A.ExpressionList m [e])

    mDeclareAssign :: (Data a, Data b, Data c, Data d) =>
                      a -> b -> c -> d -> Pattern
    mDeclareAssign n t e s
        = mSpec n (mDeclaration t) $
            mProcThenP (mAssign (mVariable n) e) $
              s

testRemoveResult :: Test
testRemoveResult = TestLabel "testRemoveResult" $ TestList
  [ -- Nothing to do
    ok    0 inner
            inner

    -- RESULT abbreviation
  , ok   10 (spec foo (A.Is m A.ResultAbbrev A.Int $ A.ActualVariable barV) inner)
            (spec foo (A.Is m A.Abbrev       A.Int $ A.ActualVariable barV) inner)

    -- RESULT retyping
  , ok   20 (spec foo (A.Retypes m A.ResultAbbrev A.Int barV) inner)
            (spec foo (A.Retypes m A.Abbrev       A.Int barV) inner)

    -- RESULT formal
  , ok   30 (A.Formal A.ResultAbbrev A.Int foo)
            (A.Formal A.Abbrev       A.Int foo)
  ]
  where
    ok :: (Alloy a (OneOp A.AbbrevMode) BaseOp
          ,Data a, Data b) => Int -> a -> b -> Test
    ok n inp exp = TestCase $ testPass ("testRemoveResult" ++ show n)
                                       exp removeResult inp setupState

    inner = A.Only m (A.Skip m)
    spec n st s = A.Spec m (A.Specification m n st) s
    foo = simpleName "foo"
    barV = A.Variable m $ simpleName "bar"

tests :: Test
tests = TestLabel "SimplifyAbbrevsTest" $ TestList
    [ testRemoveInitial
    , testRemoveResult
    ]
