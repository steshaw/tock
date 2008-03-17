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

-- | Tests for 'OccamPasses'.

module OccamPassesTest (tests) where

import Control.Monad.State
import Data.Generics
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Metadata
import qualified OccamPasses
import TestUtils

m :: Meta
m = emptyMeta

-- | Test 'OccamPasses.foldConstants'.
testFoldConstants :: Test
testFoldConstants = TestList
    [
    -- Trivial stuff
      testSame 0 one
    , testSame 1 var

    -- Things that shouldn't fold
    , testSame 10 (add var one)
    , testSame 11 (add one var)
    , testSame 12 (add var (add one var))
    , testSame 13 (add one (add var one))
    , testSame 14 (add var (add one var))

    -- Things that should fold
    , test 20 (add one one) two
    , test 21 (add one (add one one)) three
    , test 22 (add (add one one) one) three
    , test 23 (add one two) three
    , test 24 (add one (add one (add one one))) four
    , test 25 (add (add one (add one one)) one) four
    , test 26 (add (add (add one one) one) one) four

    -- Folding subexpressions of a non-constant expression
    , test 30 (add var (add one one)) (add var two)
    , test 31 (add (add one one) var) (add two var)
    , test 32 (add var (add var (add one one))) (add var (add var two))

    -- Folding existing constant variables
    , test 40 const two
    , test 41 (add const (add one one)) four
    , test 42 (add (add one one) const) four
    , test 43 (add const (add const (add one one))) six
    , test 44 (add var const) (add var two)
    , test 45 (add const var) (add two var)
    , test 46 (add const const) four
    , test 47 (add const (add var one)) (add two (add var one))
    , test 48 (add var (add const one)) (add var three)
    ]
  where
    test :: Data a => Int -> a -> a -> Test
    test n orig exp = TestCase $ testPass ("testFoldConstants" ++ show n)
                                          exp (OccamPasses.foldConstants orig)
                                          startState

    startState :: State CompState ()
    startState = defineConst "const" A.Int two

    defineConst :: String -> A.Type -> A.Expression -> State CompState ()
    defineConst s t e = defineName (simpleName s) $
        A.NameDef {
          A.ndMeta = m,
          A.ndName = "const",
          A.ndOrigName = "const",
          A.ndNameType = A.VariableName,
          A.ndType = A.IsExpr m A.ValAbbrev t e,
          A.ndAbbrevMode = A.ValAbbrev,
          A.ndPlacement = A.Unplaced
        }

    testSame :: Int -> A.Expression -> Test
    testSame n orig = test n orig orig

    add e f = A.Dyadic m A.Add e f
    var = exprVariable "var"
    const = exprVariable "const"
    one = intLiteral 1
    two = intLiteral 2
    three = intLiteral 3
    four = intLiteral 4
    six = intLiteral 6

tests :: Test
tests = TestLabel "OccamPassesTest" $ TestList
    [ testFoldConstants
    ]
