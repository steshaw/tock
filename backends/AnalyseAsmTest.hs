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

-- | Tests for 'AnalyseAsm'.

module AnalyseAsmTest (tests) where

import Test.HUnit hiding (State)

import AnalyseAsm

testParse :: Test
testParse = TestList
    [ testLine   50 "" Nothing
    , testLine   51 " " Nothing
    , testLine   52 "addl %eax, %ebx" $ Nothing

    , testLine  100 "subl $123, %esp" $ Just $ AsmStackInc 123
    , testLine  101 "addl $-123, %esp" $ Just $ AsmStackInc 123
    , testLine  102 "pushl %eax" $ Just $ AsmStackInc 4
    , testLine  103 "  pushl %eax" $ Just $ AsmStackInc 4
    , testLine  104 "pushl %eax  " $ Just $ AsmStackInc 4
    , testLine  105 "\tpushl      %eax  " $ Just $ AsmStackInc 4

    , testLine  150 "subl $123, %eax" $ Nothing
    , testLine  151 "subl $-123, %esp" $ Nothing
    , testLine  152 "addl $-123, %eax" $ Nothing
    , testLine  153 "addl $123, %esp" $ Nothing
    , testLine  154 "popl %eax" $ Nothing

    , testLine  200 "call foo" $ Just $ AsmCall "foo"
    , testLine  201 "jmp foo" $ Just $ AsmCall "foo"

    , testLine  250 "call *%eax" $ Nothing
    , testLine  251 "jmp *%eax" $ Nothing
    , testLine  252 "call .0" $ Nothing
    , testLine  253 "jmp .0" $ Nothing

    , testLine  300 "foo:" $ Just $ AsmLabel "foo"

    , testLine  350 ".blah:" $ Nothing
    , testLine  351 "0:" $ Nothing
    ]
  where
    testLine :: Int -> String -> Maybe AsmItem -> Test
    testLine n s exp = TestCase $ assertEqual ("testParse" ++ show n)
                                              exp (parseAsmLine s)

tests :: Test
tests = TestLabel "AnalyseAsmTest" $ TestList
    [ testParse
    ]
