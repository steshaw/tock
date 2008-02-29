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
    = testPP n (tts ++ [TokPreprocessor $ "#IF " ++ condition,
                        TokIdentifier "abc",
                        TokPreprocessor $ "#ENDIF"])
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

-- | Test 'expandIncludes' when we're expecting it to succeed.
testEI :: Int -> [TokenType] -> [TokenType] -> Test
testEI n itts etts = TestCase $ testPass ("testEI " ++ show n) (makeTokens etts) pass (return ())
  where
    makeTokens = zip (repeat emptyMeta)
    pass = expandIncludes (makeTokens itts)

-- | Test 'expandIncludes' when we're expecting it to fail.
testEIFail :: Int -> [TokenType] -> Test
testEIFail n itts = TestCase $ testPassShouldFail ("testEIFail " ++ show n) pass (return ())
  where
    makeTokens = zip (repeat emptyMeta)
    pass = expandIncludes (makeTokens itts)

--{{{  0xxx  simple stuff
testSimple :: Test
testSimple = TestLabel "testSimple" $ TestList
  [ testPP       0 [] []
  , testPP      10 [tp "#COMMENT blah"] []
  , testPP      20 arbitrary arbitrary
  , testPP      30 [tp "#INCLUDE \"foo\""] [IncludeFile "foo"]
  ]
  where
    tp = TokPreprocessor
    arbitrary = [Indent, Outdent, EndOfLine, TokReserved "blah", TokIdentifier "bleh"]
--}}}
--{{{  1xxx  #IF/#ELSE/#ENDIF
testIf :: Test
testIf = TestLabel "testIf" $ TestList
  -- Simple conditionals
  [ testPP 1000 [tp "#IF TRUE", ti "abc", tp "#ENDIF"]                                [ti "abc"]
  , testPP 1010 [tp "#IF FALSE", ti "abc", tp "#ENDIF"]                               []
  , testPP 1020 [tp "#IF TRUE", ti "abc", tp "#ELSE", ti "def", tp "#ENDIF"]          [ti "abc"]
  , testPP 1030 [tp "#IF FALSE", ti "abc", tp "#ELSE", ti "def", tp "#ENDIF"]         [ti "def"]
  , testPP 1040 [tp "#IF FALSE", tp "#INCLUDE \"does-not-exist.inc\"", tp "#ENDIF"]   []

  -- Nested conditionals
  , testPP 1100 [tp "#IF FALSE", tp "#IF FALSE", ti "abc", tp "#ENDIF", tp "#ENDIF"]  []
  , testPP 1110 [tp "#IF FALSE", tp "#IF TRUE", ti "abc", tp "#ENDIF", tp "#ENDIF"]   []
  , testPP 1120 [tp "#IF TRUE", tp "#IF FALSE", ti "abc", tp "#ENDIF", tp "#ENDIF"]   []
  , testPP 1130 [tp "#IF TRUE", tp "#IF TRUE", ti "abc", tp "#ENDIF", tp "#ENDIF"]    [ti "abc"]
  , testPP 1140 [tp "#IF FALSE",
                   tp "#IF FALSE", ti "abc", tp "#ELSE", ti "def", tp "#ENDIF",
                 tp "#ELSE",
                   ti "ghi",
                 tp "#ENDIF"] [ti "ghi"]
  , testPP 1150 [tp "#IF FALSE",
                   tp "#IF TRUE", ti "abc", tp "#ELSE", ti "def", tp "#ENDIF",
                 tp "#ELSE",
                   ti "ghi",
                 tp "#ENDIF"] [ti "ghi"]
  , testPP 1160 [tp "#IF TRUE",
                   tp "#IF FALSE", ti "abc", tp "#ELSE", ti "def", tp "#ENDIF",
                 tp "#ELSE",
                   ti "ghi",
                 tp "#ENDIF"] [ti "def"]
  , testPP 1170 [tp "#IF TRUE",
                   tp "#IF TRUE", ti "abc", tp "#ELSE", ti "def", tp "#ENDIF",
                 tp "#ELSE",
                   ti "ghi",
                 tp "#ENDIF"] [ti "abc"]

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
  , testPPFail 1900 [tp "#IF you can keep your head when all about you..."]
  , testPPFail 1910 [tp "#IF TRUE"]
  , testPPFail 1920 [tp "#IF TRUE love comes but once in a lifetime..."]
  , testPPFail 1930 [tp "#IF TRUE", tp "#IF FALSE", tp "#ENDIF"]
  , testPPFail 1940 [tp "#IF (TRUE", tp "#ENDIF"]
  , testPPFail 1950 [tp "#ELSE"]
  , testPPFail 1960 [tp "#ENDIF"]
  , testPPFail 1970 [tp "#IF 3 = \"foo\"", tp "#ENDIF"]
  , testPPFail 1980 [tp "#IF \"foo\" > \"bar\"", tp "#ENDIF"]
  ]
  where
    ti = TokIdentifier
    tp = TokPreprocessor
--}}}
--{{{  2xxx  #DEFINE/#UNDEF/##
testDefine :: Test
testDefine = TestLabel "testDefine" $ TestList
  -- Basic defining
  [ testPP 2000 [tp "#DEFINE FOO"] []
  , testPP 2010 [tp "#DEFINE FOO \"bar\""] []
  , testPP 2020 [tp "#DEFINE FOO 42"] []
  , testPP 2030 [tp "#UNDEF BAR"] []
  , testPP 2040 [tp "#DEFINE FOO", tp "#UNDEF FOO"] []

  -- DEFINED
  , testPPCondAfter 2100 [tp "#DEFINE FOO"] "DEFINED (FOO)"             True
  , testPPCondAfter 2110 [tp "#UNDEF FOO"] "DEFINED (FOO)"              False
  , testPPCondAfter 2120 [tp "#DEFINE FOO", tp "#UNDEF FOO"]
                         "DEFINED (FOO)"                                False
  , testPPCondAfter 2130 [tp "#UNDEF FOO", tp "#DEFINE FOO"]
                         "DEFINED (FOO)"                                True
  , testPPCond 2140 "DEFINED (COMPILER.TOCK)"                           True
  , testPPCond 2150 "NOT DEFINED (COMPILER.TOCK)"                       False

  -- Conditions involving macros
  , testPPCondAfter 2200 [tp "#DEFINE FOO 42"] "FOO = 42"               True
  , testPPCondAfter 2210 [tp "#DEFINE FOO 42"] "FOO <> 42"              False
  , testPPCondAfter 2220 [tp "#DEFINE FOO \"bar\""] "FOO = \"bar\""     True
  , testPPCondAfter 2230 [tp "#DEFINE FOO \"baz\""] "FOO = \"bar\""     False

  -- Expansion
  , testPP 2600 [tp "#DEFINE FOO \"bar\"", hh, ti "FOO"] [TokStringLiteral "bar"]
  , testPP 2610 [tp "#DEFINE FOO 1234", hh, ti "FOO"] [TokIntLiteral "1234"]

  -- Invalid definitions
  , testPPFail 2900 [tp "#DEFINE FOO", tp "#DEFINE FOO"]
  , testPPFail 2910 [tp "#DEFINE FOO !!*!%*!"]

  -- Invalid expansions
  , testPPFail 2950 [tp "#DEFINE FOO", hh, ti "FOO"]
  , testPPFail 2960 [hh, ti "FOO"]
  , testPPFail 2970 [hh, hh]
  ]
  where
    tp = TokPreprocessor
    ti = TokIdentifier
    hh = TokReserved "##"
--}}}
--{{{  3xxx  expandIncludes
testExpand :: Test
testExpand = TestLabel "testExpand" $ TestList
  [ testEI     3000 [] []
  , testEI     3010 arbitrary arbitrary

  , testEIFail 3900 [IncludeFile "this-does-not-exist", EndOfLine]
  ]
  where
    arbitrary = [Indent, Outdent, EndOfLine, TokReserved "blah", TokIdentifier "bleh"]
--}}}

tests :: Test
tests = TestLabel "PreprocessOccamTest" $ TestList
  [ testSimple
  , testIf
  , testDefine
  , testExpand
  ]
