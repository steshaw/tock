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

-- | Tests for the occam preprocessor.
module PreprocessOccamTest (tests) where

import Test.HUnit

import LexOccam
import Metadata
import PreprocessOccam
import TestUtils

-- | Test 'preprocessOccam' when we're expecting it to succeed.
testPP :: Int -> [TokenType] -> [TokenType] -> Test
testPP n itts etts = TestCase $ testPass ("testPP " ++ show n) (makeTokens etts) pass (return ())
  where
    makeTokens = zip (repeat emptyMeta)
    pass = preprocessOccam (makeTokens itts)

-- | Test a preprocessor condition string after a series of tokens.
testPPCondAfter :: Int -> [TokenType] -> String -> Bool -> Test
testPPCondAfter n tts condition exp
    = testPP n (tts ++ [TokPreprocessor $ "#IF " ++ condition, EndOfLine,
                        TokIdentifier "abc",
                        TokPreprocessor $ "#ENDIF", EndOfLine])
               (if exp then [TokIdentifier "abc"] else [])

-- | Test a preprocessor condition string.
testPPCond :: Int -> String -> Bool -> Test
testPPCond n = testPPCondAfter n []

-- | Test 'preprocessOccam' when we're expecting it to fail.
testPPFail :: Int -> [TokenType] -> Test
testPPFail n itts = TestCase $ testPassShouldFail ("testPPFail " ++ show n) pass (return ())
  where
    makeTokens = zip (repeat emptyMeta)
    pass = preprocessOccam (makeTokens itts)

--{{{  0xxx  simple stuff
testSimple :: Test
testSimple = TestLabel "testSimple" $ TestList
  [ testPP       0 [] []
  , testPP      10 [tp "#COMMENT blah", eol] []
  , testPP      20 arbitrary arbitrary
  , testPPFail 900 [tp "#INCLUDE \"this-should-not-exist.inc\"", eol]
  ]
  where
    tp = TokPreprocessor
    eol = EndOfLine
    arbitrary = [Indent, Outdent, EndOfLine, TokReserved "blah", TokIdentifier "bleh"]
--}}}
--{{{  1xxx  #IF/#ELSE/#ENDIF
testIf :: Test
testIf = TestLabel "testIf" $ TestList
  -- Simple conditionals
  [ testPP 1000 [tp "#IF TRUE",  eol, ti "abc", tp "#ENDIF", eol]                                        [ti "abc"]
  , testPP 1010 [tp "#IF FALSE", eol, ti "abc", tp "#ENDIF", eol]                                        []
  , testPP 1020 [tp "#IF TRUE",  eol, ti "abc", tp "#ELSE",  eol, ti "def", tp "#ENDIF", eol]            [ti "abc"]
  , testPP 1030 [tp "#IF FALSE", eol, ti "abc", tp "#ELSE",  eol, ti "def", tp "#ENDIF", eol]            [ti "def"]
  , testPP 1040 [tp "#IF FALSE", eol, tp "#INCLUDE \"does-not-exist.inc\"", eol, tp "#ENDIF", eol]       []

  -- Nested conditionals
  , testPP 1100 [tp "#IF FALSE", eol, tp "#IF FALSE", eol, ti "abc", tp "#ENDIF", eol, tp "#ENDIF", eol] []
  , testPP 1110 [tp "#IF FALSE", eol, tp "#IF TRUE",  eol, ti "abc", tp "#ENDIF", eol, tp "#ENDIF", eol] []
  , testPP 1120 [tp "#IF TRUE",  eol, tp "#IF FALSE", eol, ti "abc", tp "#ENDIF", eol, tp "#ENDIF", eol] []
  , testPP 1130 [tp "#IF TRUE",  eol, tp "#IF TRUE",  eol, ti "abc", tp "#ENDIF", eol, tp "#ENDIF", eol] [ti "abc"]
  , testPP 1140 [tp "#IF FALSE", eol,
                   tp "#IF FALSE", eol, ti "abc", tp "#ELSE", eol, ti "def", tp "#ENDIF", eol,
                 tp "#ELSE", eol,
                   ti "ghi",
                 tp "#ENDIF", eol] [ti "ghi"]
  , testPP 1150 [tp "#IF FALSE", eol,
                   tp "#IF TRUE", eol, ti "abc", tp "#ELSE", eol, ti "def", tp "#ENDIF", eol,
                 tp "#ELSE", eol,
                   ti "ghi",
                 tp "#ENDIF", eol] [ti "ghi"]
  , testPP 1160 [tp "#IF TRUE", eol,
                   tp "#IF FALSE", eol, ti "abc", tp "#ELSE", eol, ti "def", tp "#ENDIF", eol,
                 tp "#ELSE", eol,
                   ti "ghi",
                 tp "#ENDIF", eol] [ti "def"]
  , testPP 1170 [tp "#IF TRUE", eol,
                   tp "#IF TRUE", eol, ti "abc", tp "#ELSE", eol, ti "def", tp "#ENDIF", eol,
                 tp "#ELSE", eol,
                   ti "ghi",
                 tp "#ENDIF", eol] [ti "abc"]

  -- Expressions
  , testPPCond 1200 "FALSE AND FALSE"                            False
  , testPPCond 1210 "FALSE AND TRUE"                             False
  , testPPCond 1220 "TRUE AND FALSE"                             False
  , testPPCond 1230 "TRUE AND TRUE"                              True
  , testPPCond 1240 "FALSE OR FALSE"                             False
  , testPPCond 1250 "FALSE OR TRUE"                              True
  , testPPCond 1260 "NOT FALSE"                                  True
  , testPPCond 1270 "NOT TRUE"                                   False
  , testPPCond 1280 "(TRUE AND FALSE) OR (FALSE AND TRUE)"       False
  , testPPCond 1290 "(TRUE OR FALSE) AND (FALSE OR TRUE)"        True
  , testPPCond 1300 "NOT (FALSE AND TRUE)"                       True
  , testPPCond 1310 "3 < 4"                                      True
  , testPPCond 1320 "3 > 4"                                      False
  , testPPCond 1330 "3 <> 4"                                     True
  , testPPCond 1340 "3 = 4"                                      False
  , testPPCond 1350 "4 <= 4"                                     True
  , testPPCond 1360 "3 <= 4"                                     True
  , testPPCond 1370 "4 >= 4"                                     True
  , testPPCond 1380 "5 >= 4"                                     True
  , testPPCond 1390 "\"foo\" = \"foo\""                          True
  , testPPCond 1400 "\"foo\" <> \"foo\""                         False
  , testPPCond 1410 "\"foo\" = \"bar\""                          False
  , testPPCond 1420 "\"foo\" <> \"bar\""                         True
  , testPPCond 1430 "((3 > 4) OR (42 = 24)) AND (1 <= 2)"        False

  -- Invalid conditionals
  , testPPFail 1900 [tp "#IF you can keep your head when all about you...", eol]
  , testPPFail 1910 [tp "#IF TRUE", eol]
  , testPPFail 1920 [tp "#IF TRUE love comes but once in a lifetime...", eol]
  , testPPFail 1930 [tp "#IF TRUE", eol, tp "#IF FALSE", eol, tp "#ENDIF", eol]
  , testPPFail 1940 [tp "#IF (TRUE", eol, tp "#ENDIF", eol]
  , testPPFail 1950 [tp "#ELSE", eol]
  , testPPFail 1960 [tp "#ENDIF", eol]
  , testPPFail 1970 [tp "#IF 3 = \"foo\"", eol, tp "#ENDIF", eol]
  , testPPFail 1980 [tp "#IF \"foo\" > \"bar\"", eol, tp "#ENDIF", eol]
  ]
  where
    ti = TokIdentifier
    tp = TokPreprocessor
    eol = EndOfLine
--}}}
--{{{  2xxx  #DEFINE/#UNDEF/##
testDefine :: Test
testDefine = TestLabel "testDefine" $ TestList
  -- Basic defining
  [ testPP 2000 [tp "#DEFINE FOO", eol] []
  , testPP 2010 [tp "#DEFINE FOO \"bar\"", eol] []
  , testPP 2020 [tp "#DEFINE FOO 42", eol] []
  , testPP 2030 [tp "#UNDEF BAR", eol] []
  , testPP 2040 [tp "#DEFINE FOO", eol, tp "#UNDEF FOO", eol] []

  -- DEFINED
  , testPPCondAfter 2100 [tp "#DEFINE FOO", eol] "DEFINED (FOO)"             True
  , testPPCondAfter 2110 [tp "#UNDEF FOO", eol] "DEFINED (FOO)"              False
  , testPPCondAfter 2120 [tp "#DEFINE FOO", eol, tp "#UNDEF FOO", eol]
                         "DEFINED (FOO)"                                     False
  , testPPCondAfter 2130 [tp "#UNDEF FOO", eol, tp "#DEFINE FOO", eol]
                         "DEFINED (FOO)"                                     True
  , testPPCond 2140 "DEFINED (COMPILER.TOCK)"                                True
  , testPPCond 2150 "NOT DEFINED (COMPILER.TOCK)"                            False

  -- Conditions involving macros
  , testPPCondAfter 2200 [tp "#DEFINE FOO 42", eol] "FOO = 42"               True
  , testPPCondAfter 2210 [tp "#DEFINE FOO 42", eol] "FOO <> 42"              False
  , testPPCondAfter 2220 [tp "#DEFINE FOO \"bar\"", eol] "FOO = \"bar\""     True
  , testPPCondAfter 2230 [tp "#DEFINE FOO \"baz\"", eol] "FOO = \"bar\""     False

  -- Expansion
  , testPP 2600 [tp "#DEFINE FOO \"bar\"", eol, hh, ti "FOO"] [TokStringLiteral "bar"]
  , testPP 2610 [tp "#DEFINE FOO 1234", eol, hh, ti "FOO"] [TokIntLiteral "1234"]

  -- Invalid definitions
  , testPPFail 2900 [tp "#DEFINE FOO", eol, tp "#DEFINE FOO", eol]
  , testPPFail 2910 [tp "#DEFINE FOO !!*!%*!", eol]

  -- Invalid expansions
  , testPPFail 2950 [tp "#DEFINE FOO", eol, hh, ti "FOO"]
  , testPPFail 2960 [hh, ti "FOO"]
  , testPPFail 2970 [hh, hh]
  ]
  where
    tp = TokPreprocessor
    ti = TokIdentifier
    hh = TokReserved "##"
    eol = EndOfLine
--}}}

tests :: Test
tests = TestLabel "PreprocessOccamTest" $ TestList
  [ testSimple
  , testIf
  , testDefine
  ]
