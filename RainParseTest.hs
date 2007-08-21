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

module RainParseTest (tests) where

import qualified RainParse as RP
import qualified AST as A
import Text.ParserCombinators.Parsec (runParser,eof)
import Test.HUnit
import Metadata (Meta,emptyMeta)
import Prelude hiding (fail)
import TestUtil
import Pattern
import TreeUtil
import CompState

data ParseTest a = Show a => ExpPass (String, RP.RainParser a , (a -> Assertion)) | ExpFail (String, RP.RainParser a)

pass :: Show a => (String, RP.RainParser a , (a -> Assertion)) -> ParseTest a
pass x = ExpPass x

fail :: Show a => (String, RP.RainParser a) -> ParseTest a
fail x = ExpFail x


--Runs a parse test, given a tuple of: (source text, parser function, assert)
testParsePass :: Show a => (String, RP.RainParser a , (a -> Assertion)) -> Assertion
testParsePass (text,prod,test)
    = case (runParser parser emptyState "" text) of
        Left error -> assertString (show error)
        Right result -> ((return result) >>= test)
    where parser = do { p <- prod ; eof ; return p}
    --Adding the eof parser above ensures that all the input is consumed from a test.  Otherwise
    --tests such as "seq {}}" would succeed, because the final character simply wouldn't be parsed -
    --which would ruin the point of the test

testParseFail :: Show a => (String, RP.RainParser a) -> Assertion
testParseFail (text,prod)
    = case (runParser parser emptyState "" text) of
        Left error -> return ()
        Right result -> assertFailure ("Test was expected to fail:\n***BEGIN CODE***\n" ++ text ++ "\n*** END CODE ***\n")
    where parser = do { p <- prod ; eof ; return p}
testExp0 = pass ("b",RP.expression,      
  assertEqual "Variable Expression Test" (exprVariable "b") )

testExp1 = pass ("b == c",RP.expression,      
  assertEqual "Operator Expression Test" $ A.Dyadic emptyMeta A.Eq (exprVariable "b") (exprVariable "c") )

--Helper function for ifs:
makeIf :: [(A.Expression,A.Process)] -> A.Process
makeIf list = A.If m $ A.Several m (map makeChoice list)
  where
    makeChoice :: (A.Expression,A.Process) -> A.Structured
    makeChoice (exp,proc) = A.OnlyC m $ A.Choice m exp proc

dyExp :: A.DyadicOp -> A.Variable -> A.Variable -> A.Expression
dyExp op v0 v1 = A.Dyadic m op (A.ExprVariable m v0) (A.ExprVariable m v1)

testIf :: [ParseTest A.Process]
testIf =
 [
  pass ("if (a) ;",RP.statement,
    assertEqual "If Test 0" $ makeIf [(exprVariable "a",A.Skip m),(A.True m,A.Skip m)])
  ,pass ("if (a) ; else ;",RP.statement,
    assertEqual "If Test 1" $ makeIf [(exprVariable "a",A.Skip m),(A.True m,A.Skip m)])
  ,pass ("if (a) ; else a = b;",RP.statement,
    assertEqual "If Test 2" $ makeIf [(exprVariable "a",A.Skip m),(A.True m,makeSimpleAssign "a" "b")])    
  ,pass ("if (a) ; else if (b) ; ",RP.statement,
    assertEqual "If Test 3" $ makeIf [(exprVariable "a",A.Skip m),(A.True m,makeIf [(exprVariable "b",A.Skip m),(A.True m,A.Skip m)])])
  ,pass ("if (a) ; else if (b) ; else ; ",RP.statement,
    assertEqual "If Test 4" $ makeIf [(exprVariable "a",A.Skip m),(A.True m,makeIf [(exprVariable "b",A.Skip m),(A.True m,A.Skip m)])])    
  ,pass ("if (a) c = d; else if (b) e = f; else g = h;",RP.statement,
    assertEqual "If Test 5" $ makeIf [(exprVariable "a",makeSimpleAssign "c" "d"),(A.True m,makeIf [(exprVariable "b",makeSimpleAssign "e" "f"),(A.True m,makeSimpleAssign "g" "h")])])    
  --TODO add fail tests, maybe {} brackets
 ]

testAssign :: [ParseTest A.Process]
testAssign =
 [
  pass ("a = b;",RP.statement,
    assertEqual "Assign Test 0" $ makeSimpleAssign "a" "b")
  ,fail ("a != b;",RP.statement)
  ,pass ("a += b;",RP.statement,
    assertEqual "Assign Test 1" $ makeAssign (variable "a") (dyExp A.Plus (variable ("a")) (variable ("b")) ) )
  ,fail ("a + = b;",RP.statement)
 ]

testWhile :: [ParseTest A.Process]
testWhile = 
 [
  pass ("while (a) ;",RP.statement, 
        assertEqual "While Test" $ A.While emptyMeta (exprVariable "a") (A.Skip emptyMeta) )
  ,fail ("while (a)",RP.statement)
  ,fail ("while () ;",RP.statement)
  ,fail ("while () {}",RP.statement)
  ,fail ("while ;",RP.statement)
  ,fail ("while {}",RP.statement)
  ,fail ("while ",RP.statement)
 ]

testSeq :: [ParseTest A.Process]
testSeq =
 [
  pass ("seq { }",RP.statement,
    assertEqual "Empty Seq Test" $ A.Seq m $ A.Several m [] )
  ,pass ("seq { ; ; }",RP.statement,
    assertEqual "Seq Skip Test" $ A.Seq m $ A.Several m [(A.OnlyP m (A.Skip m)),(A.OnlyP m (A.Skip m))] )

  ,pass ("{ }",RP.statement,
    assertEqual "Empty Unlabelled-Seq Test" $ A.Seq m $ A.Several m [] )

  ,pass ("{ ; ; }",RP.statement,
    assertEqual "Unlabelled-Seq Skip Test" $ A.Seq m $ A.Several m [(A.OnlyP m (A.Skip m)),(A.OnlyP m (A.Skip m))] )

  ,pass ("{ { } }",RP.statement,
    assertEqual "Unlabelled-Seq Nest Test 0" $ A.Seq m $ A.Several m [A.OnlyP m $ A.Seq m (A.Several m [])] )
  ,pass ("seq { { } }",RP.statement,
    assertEqual "Unlabelled-Seq Nest Test 1" $ A.Seq m $ A.Several m [A.OnlyP m $ A.Seq m (A.Several m [])] )
  ,pass ("{ seq { } }",RP.statement,
    assertEqual "Unlabelled-Seq Nest Test 2" $ A.Seq m $ A.Several m [A.OnlyP m $ A.Seq m (A.Several m [])] )        

  ,pass ("{ ; {} }",RP.statement,
    assertEqual "Unlabelled-Seq Nest Test 3" $ A.Seq m $ A.Several m [(A.OnlyP m (A.Skip m)),(A.OnlyP m $ A.Seq m (A.Several m []))] )

  ,pass ("seq { ; {} }",RP.statement,
    assertEqual "Unlabelled-Seq Nest Test 4" $ A.Seq m $ A.Several m [(A.OnlyP m (A.Skip m)),(A.OnlyP m $ A.Seq m (A.Several m []))] )

  ,pass ("{ ; seq {} }",RP.statement,
    assertEqual "Unlabelled-Seq Nest Test 5" $ A.Seq m $ A.Several m [(A.OnlyP m (A.Skip m)),(A.OnlyP m $ A.Seq m (A.Several m []))] )

  ,fail ("seq",RP.statement)
  ,fail ("seq ;",RP.statement)
  ,fail ("seq {",RP.statement)
  ,fail ("seq }",RP.statement)
  ,fail ("{",RP.statement)
  ,fail ("}",RP.statement)
  ,fail ("seq seq {}",RP.statement)
  ,fail ("seq seq",RP.statement)  
  ,fail ("seq {}}",RP.statement)
  ,fail ("seq {{}",RP.statement)
  --should fail, because it is two statements, not one:
  ,fail ("seq {};",RP.statement)
  ,fail ("{};",RP.statement)
  
 ]

testPar :: [ParseTest A.Process]
testPar =
 [
  pass ("par { }",RP.statement,
    assertEqual "Empty Par Test" $ A.Par m A.PlainPar $ A.Several m [] )

  ,pass ("par { ; ; }",RP.statement,
    assertEqual "Par Skip Test" $ A.Par m A.PlainPar $ A.Several m [(A.OnlyP m (A.Skip m)),(A.OnlyP m (A.Skip m))] )      
 ]
        
testEach :: [ParseTest A.Process]
testEach =
 [
  pass ("seqeach (c : \"1\") c = 7;", RP.statement,
    assertEqual "Each Test 0" $ A.Seq m $ A.Rep m (A.ForEach m (simpleName "c") (makeLiteralString "1")) $    
      A.OnlyP m $ (makeAssign (variable "c") (A.Literal m A.Int (A.IntLiteral m "7"))) )
  ,pass ("pareach (c : \"345\") {c = 1; c = 2;}", RP.statement,
    assertEqual "Each Test 1" $ A.Par m A.PlainPar $ A.Rep m (A.ForEach m (simpleName "c") (makeLiteralString "345")) $ 
      A.OnlyP m $ makeSeq[(makeAssign (variable "c") (A.Literal m A.Int (A.IntLiteral m "1"))),(makeAssign (variable "c") (A.Literal m A.Int (A.IntLiteral m "2")))] )      
 ]

testTopLevelDecl :: [ParseTest A.Structured]
testTopLevelDecl =
 [
  pass ("process noargs() {}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 0" $ tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "noargs") $ tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal])
        (tag2 A.Seq DontCare $ tag2 A.Several DontCare ([] :: [A.Structured]))
      )
      (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
  )
  , pass ("process onearg(int: x) {x = 0;}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 1" $ tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "onearg") $ tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Int64 (simpleNamePattern "x")]
        (tag2 A.Seq DontCare $ tag2 A.Several DontCare [tag2 A.OnlyP DontCare $ makeAssignPattern (variablePattern "x") (intLiteralPattern 0)]) )
      (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
  )
  , fail ("process", RP.topLevelDecl)
  , fail ("process () {}", RP.topLevelDecl)
  , fail ("process foo", RP.topLevelDecl)
  , fail ("process foo ()", RP.topLevelDecl)
  , fail ("process foo () {", RP.topLevelDecl)
  , fail ("process foo ( {} )", RP.topLevelDecl)
  , fail ("process foo (int: x)", RP.topLevelDecl)
  , fail ("process foo (int x) {}", RP.topLevelDecl)
    
 ]

nonShared :: A.ChanAttributes
nonShared = A.ChanAttributes { A.caWritingShared = False, A.caReadingShared = False}

testDataType :: [ParseTest A.Type]
testDataType =
 [
  pass ("bool",RP.dataType,assertEqual "testDataType 0" A.Bool)
  ,pass ("int",RP.dataType,assertEqual "testDataType 1" A.Int64)
  ,fail ("boolean",RP.dataType)
  
  ,pass ("?int",RP.dataType,assertEqual "testDataType 2" $ A.Chan A.DirInput nonShared A.Int64)
  ,pass ("! bool",RP.dataType,assertEqual "testDataType 3" $ A.Chan A.DirOutput nonShared A.Bool)
  --These types should succeed in the *parser* -- they would be thrown out further down the line:
  ,pass ("??int",RP.dataType,assertEqual "testDataType 4" $ A.Chan A.DirInput nonShared $ A.Chan A.DirInput nonShared A.Int64)
  ,pass ("? ? int",RP.dataType,assertEqual "testDataType 4" $ A.Chan A.DirInput nonShared $ A.Chan A.DirInput nonShared A.Int64)
  ,pass ("!!bool",RP.dataType,assertEqual "testDataType 5" $ A.Chan A.DirOutput nonShared $ A.Chan A.DirOutput nonShared A.Bool)  
  ,pass ("?!bool",RP.dataType,assertEqual "testDataType 6" $ A.Chan A.DirInput nonShared $ A.Chan A.DirOutput nonShared A.Bool)  
  
  ,fail ("?",RP.dataType)
  ,fail ("!",RP.dataType)
  ,fail ("??",RP.dataType)
  ,fail ("int?",RP.dataType)
  ,fail ("bool!",RP.dataType)
  ,fail ("int?int",RP.dataType)
  
  
 ]
        
--Returns the list of tests:
tests :: Test
tests = TestList
 [
  parseTest testExp0,parseTest testExp1,
  parseTests testWhile,
  parseTests testSeq,
  parseTests testPar,
  parseTests testEach,
  parseTests testIf,
  parseTests testAssign,
  parseTests testDataType,
  parseTests testTopLevelDecl
 ]
--TODO test:
-- input (incl. ext input)
-- output
-- alting
--TODO later on:
-- types (lists, tuples, maps)
-- functions
-- typedefs


  where
    parseTest :: Show a => ParseTest a -> Test
    parseTest (ExpPass test) = TestCase (testParsePass test)
    parseTest (ExpFail test) = TestCase (testParseFail test)
    parseTests :: Show a => [ParseTest a] -> Test
    parseTests tests = TestList (map parseTest tests)

