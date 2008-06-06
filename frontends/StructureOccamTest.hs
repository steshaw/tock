{-
Tock: a compiler for parallel languages
Copyright (C) 2008  Adam Sampson <ats@offog.org>

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

-- | Tests for the occam structure analyser.
module StructureOccamTest (tests) where

import Test.HUnit

import LexOccam
import Metadata
import Pattern
import StructureOccam
import TestUtils
import TreeUtils

-- | Test 'structureOccam' when we're expecting it to succeed.
testS :: Int -> [Token] -> [Pattern] -> Test
testS n its ets = TestCase $ testPass' ("testS " ++ show n) ets (structureOccam its) (return ())

-- | Test 'structureOccam' when we're expecting it to fail.
testSFail :: Int -> [Token] -> Test
testSFail n its = TestCase $ testPassShouldFail' ("testSFail " ++ show n) (structureOccam its) (return ())

--{{{  0xxx  simple stuff
testSimple :: Test
testSimple = TestLabel "testSimple" $ TestList
  -- Basic structuring
  [ testS       0 []
                  []
  , testS      10 [t 1 1 foo, t 2 1 foo]
                  [fooP, eolP, fooP, eolP]
  , testS      20 [t 1 1 foo, t 2 3 foo]
                  [fooP, eolP, inP, fooP, eolP, outP]
  , testS      30 [t 1 1 foo, t 2 3 foo, t 3 1 foo]
                  [fooP, eolP, inP, fooP, eolP, outP, fooP, eolP]
  , testS      40 [t 1 1 foo, t 2 3 foo, t 3 5 foo, t 4 1 foo]
                  [fooP, eolP, inP, fooP, eolP, inP, fooP, eolP, outP, outP, fooP, eolP]
  , testS      50 [t 1 1 foo, t 2 3 foo, t 3 3 foo, t 4 3 foo]
                  [fooP, eolP, inP, fooP, eolP, fooP, eolP, fooP, eolP, outP]

  -- Ignoring include markers
  , testS     100 [t 1 1 (IncludeFile "bar"), t 2 1 foo]
                  [tag2 Token DontCare $ tag1 IncludeFile "bar", eolP, fooP, eolP]

  -- Things that should fail
  , testSFail  900 [t 1 1 foo, t 2 2 foo]
  , testSFail  910 [t 1 1 foo, t 2 5 foo]
  ]
  where
    foo = TokIdentifier "foo"
    fooP = tag2 Token DontCare $ tag1 TokIdentifier "foo"
    eolP = tag2 Token DontCare $ tag0 EndOfLine
    inP = tag2 Token DontCare $ tag0 Indent
    outP = tag2 Token DontCare $ tag0 Outdent
    t l c tt = Token (emptyMeta { metaFile = Just "simulated.occ"
                                , metaLine = l
                                , metaColumn = c
                                })
                     tt
--}}}

tests :: Test
tests = TestLabel "StructureOccamTest" $ TestList
  [ testSimple
  ]
