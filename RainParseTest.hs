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
import qualified LexRain as L
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
  = do lexOut <- (L.runLexer "<test>" text)
       case lexOut of
         Left m -> assertFailure $ "Parse error in:\n" ++ text ++ "\n***at: " ++ (show m)
         Right toks -> case (runParser parser emptyState "<test>" toks) of
                         Left error -> assertFailure $  "Parse error in:\n" ++ text ++ "\n***" ++ (show error)
                         Right result -> ((return result) >>= test)
    where parser = do { p <- prod ; eof ; return p}
    --Adding the eof parser above ensures that all the input is consumed from a test.  Otherwise
    --tests such as "seq {}}" would succeed, because the final character simply wouldn't be parsed -
    --which would ruin the point of the test

testParseFail :: Show a => (String, RP.RainParser a) -> Assertion
testParseFail (text,prod)
    = do lexOut <- (L.runLexer "<test>" text)
         case lexOut of
           Left error -> return ()
           Right toks -> case (runParser parser emptyState "<test>" toks) of
                           Left error -> return ()
                           Right result -> assertFailure ("Test was expected to fail:\n***BEGIN CODE***\n" ++ text ++ "\n*** END CODE ***\n")
    where parser = do { p <- prod ; eof ; return p}


data ExprHelper = 
  Dy ExprHelper A.DyadicOp ExprHelper
  | Mon A.MonadicOp ExprHelper
  | Cast A.Type ExprHelper
  | Var String
  | DirVar A.Direction String
  | Lit A.Expression

buildExprPattern :: ExprHelper -> Pattern
buildExprPattern (Dy lhs op rhs) = tag4 A.Dyadic DontCare op (buildExprPattern lhs) (buildExprPattern rhs)
buildExprPattern (Mon op rhs) = tag3 A.Monadic DontCare op (buildExprPattern rhs)
buildExprPattern (Cast ty rhs) = tag4 A.Conversion DontCare A.DefaultConversion (stopCaringPattern m $ mkPattern ty) (buildExprPattern rhs)
buildExprPattern (Var n) = tag2 A.ExprVariable DontCare $ variablePattern n
buildExprPattern (DirVar dir n) = tag2 A.ExprVariable DontCare $ (stopCaringPattern m $ tag3 A.DirectedVariable DontCare dir $ variablePattern n)
buildExprPattern (Lit e) = (stopCaringPattern m) $ mkPattern e


--You are allowed to chain arithmetic operators without brackets, but not comparison operators
-- (the meaning of "b == c == d" is obscure enough to be dangerous, even if it passes the type checker)
--All arithmetic operators bind at the same level, which is a closer binding than all comparison operators.
--To clear that up, here's some BNF:
-- expression ::= comparisonExpression | subExpr | dataType ":" expression | "?" expression | "!" expression
-- comparsionExpression ::= subExpr comparisonOp subExpr
-- subExpr ::= exprItem | monadicArithOp subExpr | subExpr dyadicArithOp subExpr | "(" expression ")"
-- exprItem ::= identifier | literal

-- Partially left-factor subExpr:
--subExpr ::= subExpr' | subExpr' dyadicArithOp subExpr
--subExpr' ::= exprItem | monadicArithOp subExpr' | "(" expression ")"


testExprs :: [ParseTest A.Expression]
testExprs =
 [
  --Just a variable:
  passE ("b", -1, Var "b" )

  --Dyadic operators:
  ,passE ("b + c", 0 ,Dy (Var "b") A.Plus (Var "c") )
  ,passE ("b % c", 0 ,Dy (Var "b") A.Rem (Var "c") )
  ,passE ("b == c", 1 ,Dy (Var "b") A.Eq (Var "c") )
  ,passE ("(b + c)", 2 ,Dy (Var "b") A.Plus (Var "c") )
  ,passE ("(b == c)", 3 ,Dy (Var "b") A.Eq (Var "c") )
  ,passE ("((b + c))", 4 ,Dy (Var "b") A.Plus (Var "c") )
  ,passE ("((b == c))", 5 ,Dy (Var "b") A.Eq (Var "c") )
  ,passE ("b - c", 6 ,Dy (Var "b") A.Minus (Var "c" ))
  ,passE ("b + c + d", 7, Dy (Dy (Var "b") A.Plus (Var "c")) A.Plus (Var "d") )
  ,passE ("(b + c) + d", 8, Dy (Dy (Var "b") A.Plus (Var "c")) A.Plus (Var "d") )
  ,passE ("b + (c + d)", 9, Dy (Var "b") A.Plus (Dy (Var "c") A.Plus (Var "d")) )

  ,passE ("b - c * d / e", 10, Dy (Dy (Dy (Var "b") A.Minus (Var "c")) A.Times (Var "d")) A.Div (Var "e") )

  ,passE ("b + c == d * e", 11, Dy (Dy (Var "b") A.Plus (Var "c")) A.Eq (Dy (Var "d") A.Times (Var "e")) )
  ,passE ("(b + c) == d * e", 12, Dy (Dy (Var "b") A.Plus (Var "c")) A.Eq (Dy (Var "d") A.Times (Var "e")) )
  ,passE ("b + c == (d * e)", 13, Dy (Dy (Var "b") A.Plus (Var "c")) A.Eq (Dy (Var "d") A.Times (Var "e")) )
  ,passE ("(b + c) == (d * e)", 14, Dy (Dy (Var "b") A.Plus (Var "c")) A.Eq (Dy (Var "d") A.Times (Var "e")) )
  ,passE ("(b == c) + (d == e)", 15, Dy (Dy (Var "b") A.Eq (Var "c")) A.Plus (Dy (Var "d") A.Eq (Var "e")) )
  ,passE ("(b == c) + d == e", 16, Dy (Dy (Dy (Var "b") A.Eq (Var "c")) A.Plus (Var "d")) A.Eq (Var "e") )
  ,passE ("(b == c) == (d == e)", 17, Dy (Dy (Var "b") A.Eq (Var "c")) A.Eq (Dy (Var "d") A.Eq (Var "e")) )
  ,passE ("(b == c) == d", 18, Dy (Dy (Var "b") A.Eq (Var "c")) A.Eq (Var "d") )

  ,failE ("b == c + d == e")
  ,failE ("b == c == d")
  ,failE ("b < c < d")
  ,failE ("b + c == d + e <= f")

  --Monadic operators:

  ,passE ("-b", 101, Mon A.MonadicMinus (Var "b") )
  ,failE ("+b")
  ,passE ("a - - b", 102, Dy (Var "a") A.Minus (Mon A.MonadicMinus $ Var "b") )
  ,passE ("a--b", 103, Dy (Var "a") A.Minus (Mon A.MonadicMinus $ Var "b") )
  ,passE ("a---b", 104, Dy (Var "a") A.Minus (Mon A.MonadicMinus $ Mon A.MonadicMinus $ Var "b") )
  ,passE ("-b+c", 105, Dy (Mon A.MonadicMinus $ Var "b") A.Plus (Var "c") )
  ,passE ("c+-b", 106, Dy (Var "c") A.Plus (Mon A.MonadicMinus $ Var "b") )
  ,passE ("-(b+c)", 107, Mon A.MonadicMinus $ Dy (Var "b") A.Plus (Var "c") )

  --Casting:

  ,passE ("bool: b", 201, Cast A.Bool (Var "b"))
  ,passE ("mytype: b", 202, Cast (A.UserDataType $ typeName "mytype") (Var "b"))
    --Should at least parse:
  ,passE ("uint8 : true", 203, Cast A.Byte $ Lit (A.True m) )
  ,passE ("uint8 : b == c", 204, Cast A.Byte $ Dy (Var "b") A.Eq (Var "c") )
  ,passE ("uint8 : b + c", 205, Cast A.Byte $ Dy (Var "b") A.Plus (Var "c") )
  ,passE ("uint8 : b + c == d * e", 206, Cast A.Byte $ Dy (Dy (Var "b") A.Plus (Var "c")) A.Eq (Dy (Var "d") A.Times (Var "e")) )
  ,passE ("uint8 : b + (uint8 : c)", 207, Cast A.Byte $ Dy (Var "b") A.Plus (Cast A.Byte $ Var "c") )
  ,passE ("(uint8 : b) + (uint8 : c)", 208, Dy (Cast A.Byte $ Var "b") A.Plus (Cast A.Byte $ Var "c") )
  ,passE ("uint8 : b == (uint8 : c)", 209, Cast A.Byte $ Dy (Var "b") A.Eq (Cast A.Byte $ Var "c") )
  ,passE ("(uint8 : b) == (uint8 : c)", 210, Dy (Cast A.Byte $ Var "b") A.Eq (Cast A.Byte $ Var "c") )
  ,failE ("uint8 : b + uint8 : c")
  ,failE ("uint8 : b == uint8 : c")
  ,failE ("(uint8 : b) + uint8 : c")
  ,failE ("(uint8 : b) == uint8 : c")
  
  ,passE ("?uint8: ?c", 240, Cast (A.Chan A.DirInput nonShared A.Byte) $ DirVar A.DirInput "c")
  --Should parse:
  ,passE ("?c: ?c", 241, Cast (A.Chan A.DirInput nonShared $ A.UserDataType $ typeName "c") $ DirVar A.DirInput "c")
  ,passE ("?c: ?c : b", 242, Cast (A.Chan A.DirInput nonShared $ A.UserDataType $ typeName "c") $ 
                               Cast (A.Chan A.DirInput nonShared $ A.UserDataType $ typeName "c") $ Var "b")
  ,failE ("?c:")
  ,failE (":?c")
 ]
 where
   passE :: (String,Int,ExprHelper) -> ParseTest A.Expression
   passE (code,index,expr) = pass(code,RP.expression,assertPatternMatch ("testExprs " ++ show index) (buildExprPattern expr))
   failE x = fail (x,RP.expression)

testLiteral :: [ParseTest A.Expression]
testLiteral =
 [
  --Int literals: 
  pass ("0", RP.literal, assertEqual "testLiteral 0" (intLiteral 0))
  --2^32:
  ,pass ("4294967296", RP.literal, assertEqual "testLiteral 1" (intLiteral 4294967296))
  --2^64:
  ,pass ("18446744073709551616", RP.literal, assertEqual "testLiteral 2" (intLiteral 18446744073709551616))  
  --2^100:  We should be able to parse this, but it will be rejected at a later stage:
  ,pass ("1267650600228229401496703205376", RP.literal, assertEqual "testLiteral 3" (intLiteral 1267650600228229401496703205376))  
  --Test that both literal and expression parse -3 the same way:
  ,pass ("-3", RP.literal, assertEqual "testLiteral 4" (intLiteral (-3)))
  ,pass ("-3", RP.expression, assertEqual "testLiteral 5" (intLiteral (-3)))
  
  --Non-integers currently unsupported:
  ,fail ("0.",RP.literal)
  ,fail ("0.0",RP.literal)
  ,fail (".0",RP.literal)
  ,fail ("0x0",RP.literal)
  ,fail ("0a0",RP.literal)
  ,fail ("0a",RP.literal)
  
  --Identifiers are not literals (except true and false):
  ,pass ("true", RP.literal, assertEqual "testLiteral 100" (A.True m))
  ,pass ("false", RP.literal, assertEqual "testLiteral 101" (A.False m))
  ,fail ("x",RP.literal)
  ,fail ("x0",RP.literal)
  ,fail ("TRUE",RP.literal)
  ,fail ("FALSE",RP.literal)
    
  --Strings:
  ,pass ("\"\"", RP.literal, assertPatternMatch "testLiteral 201" $ makeLiteralStringPattern "")
  ,pass ("\"abc\"", RP.literal, assertPatternMatch "testLiteral 202" $ makeLiteralStringPattern "abc")
  ,pass ("\"abc\\n\"", RP.literal, assertPatternMatch "testLiteral 203" $ makeLiteralStringPattern "abc\n")
  ,pass ("\"a\\\"bc\"", RP.literal, assertPatternMatch "testLiteral 204" $ makeLiteralStringPattern "a\"bc")
  ,fail ("\"",RP.literal)
  ,fail ("\"\"\"",RP.literal)
  ,fail ("a\"\"",RP.literal)
  ,fail ("\"\"a",RP.literal)
  ,fail ("\"\\\"",RP.literal)
  
 ]

testRange :: [ParseTest A.Expression]
testRange =
 [
  pass("[0..1]", RP.expression, assertPatternMatch "testRange 0" $ tag2 A.ExprConstr DontCare $ tag3 A.RangeConstr DontCare (intLiteralPattern 0) (intLiteralPattern 1))
  ,pass("[0..10000]", RP.expression, assertPatternMatch "testRange 0" $ tag2 A.ExprConstr DontCare $ tag3 A.RangeConstr DontCare (intLiteralPattern 0) (intLiteralPattern 10000))
  ,pass("[-3..-1]", RP.expression, assertPatternMatch "testRange 0" $ tag2 A.ExprConstr DontCare $ tag3 A.RangeConstr DontCare (intLiteralPattern $ -3) (intLiteralPattern $ -1))
  --For now, at least, this should fail:
  ,fail("[0..x]", RP.expression)
 ]

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

-- | Test innerBlock, particularly with declarations mixed with statements:
testBlock :: [ParseTest A.Structured]
testBlock =
 [
  pass("{ a = b; }",RP.innerBlock,assertPatternMatch "testBlock 0" (tag2 A.Several DontCare [tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "a" "b"]) )
  ,pass("{ a = b; b = c; }",RP.innerBlock,assertPatternMatch "testBlock 1" (tag2 A.Several DontCare 
    [tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "a" "b",tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "b" "c"]) )
  ,pass("{ uint8: x; a = b; }",RP.innerBlock,assertPatternMatch "testBlock 2" $ tag2 A.Several DontCare [tag3 A.Spec DontCare 
    (tag3 A.Specification DontCare (simpleNamePattern "x") $ tag2 A.Declaration DontCare A.Byte) $ tag2 A.Several DontCare 
    [tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "a" "b"]
   ])
  ,pass("{ uint8: x; a = b; b = c; }",RP.innerBlock,assertPatternMatch "testBlock 3" $ tag2 A.Several DontCare [tag3 A.Spec DontCare 
    (tag3 A.Specification DontCare (simpleNamePattern "x") $ tag2 A.Declaration DontCare A.Byte) $ tag2 A.Several DontCare 
    [tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "a" "b",tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "b" "c"]
   ])   
  ,pass("{ b = c; uint8: x; a = b; }",RP.innerBlock,assertPatternMatch "testBlock 4" $ tag2 A.Several DontCare [tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "b" "c",
    tag3 A.Spec DontCare 
      (tag3 A.Specification DontCare (simpleNamePattern "x") $ tag2 A.Declaration DontCare A.Byte) $ tag2 A.Several DontCare 
    [tag2 A.OnlyP DontCare $ makeSimpleAssignPattern "a" "b"]
   ])
  ,fail("{b}",RP.innerBlock)
 ]
        
testEach :: [ParseTest A.Process]
testEach =
 [
  pass ("seqeach (c : \"1\") c = 7;", RP.statement,
    assertPatternMatch  "Each Test 0" (stopCaringPattern m $ mkPattern $ A.Seq m $ A.Rep m (A.ForEach m (simpleName "c") (makeLiteralString "1")) $    
      A.OnlyP m $ (makeAssign (variable "c") (A.Literal m A.Int (A.IntLiteral m "7"))) ))
  ,pass ("pareach (c : \"345\") {c = 1; c = 2;}", RP.statement,
    assertEqual "Each Test 1" $ A.Par m A.PlainPar $ A.Rep m (A.ForEach m (simpleName "c") (makeLiteralString "345")) $ 
      A.OnlyP m $ makeSeq[(makeAssign (variable "c") (A.Literal m A.Int (A.IntLiteral m "1"))),(makeAssign (variable "c") (A.Literal m A.Int (A.IntLiteral m "2")))] )      
 ]

testTopLevelDecl :: [ParseTest A.Structured]
testTopLevelDecl =
 [
  pass ("process noargs() {}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 0" $ tag2 A.Several DontCare [tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "noargs") $ tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal])
        (tag2 A.Seq DontCare $ tag2 A.Several DontCare ([] :: [A.Structured]))
      )
      (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)]
  )
  , pass ("process noargs() par {}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 0b" $ tag2 A.Several DontCare [tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "noargs") $ tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal])
        (tag3 A.Par DontCare A.PlainPar $ tag2 A.Several DontCare ([] :: [A.Structured]))
      )
      (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)]
  )
  
  , pass ("process onearg(int: x) {x = 0;}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 1" $ tag2 A.Several DontCare [tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "onearg") $ tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Int (simpleNamePattern "x")]
        (tag2 A.Seq DontCare $ tag2 A.Several DontCare [tag2 A.OnlyP DontCare $ makeAssignPattern (variablePattern "x") (intLiteralPattern 0)]) )
      (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)]
  )
  ,pass ("process noargs0() {} process noargs1 () {}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 2" $ tag2 A.Several DontCare [
      tag3 A.Spec DontCare 
        (tag3 A.Specification DontCare (simpleNamePattern "noargs0") $ tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal])
          (tag2 A.Seq DontCare $ tag2 A.Several DontCare ([] :: [A.Structured]))
        ) (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
      ,tag3 A.Spec DontCare 
        (tag3 A.Specification DontCare (simpleNamePattern "noargs1") $ tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal])
          (tag2 A.Seq DontCare $ tag2 A.Several DontCare ([] :: [A.Structured]))
        ) (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
      ]
  )  
  , fail ("process", RP.topLevelDecl)
  , fail ("process () {}", RP.topLevelDecl)
  , fail ("process foo", RP.topLevelDecl)
  , fail ("process foo ()", RP.topLevelDecl)
  , fail ("process foo () {", RP.topLevelDecl)
  , fail ("process foo ( {} )", RP.topLevelDecl)
  , fail ("process foo (int: x)", RP.topLevelDecl)
  , fail ("process foo (int x) {}", RP.topLevelDecl)
    
    
  ,pass ("function uint8: cons() {}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 100" $ tag2 A.Several DontCare [tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "cons") $
        tag5 A.Function DontCare A.PlainSpec [A.Byte] ([] :: [A.Formal]) $
          (tag2 A.OnlyP DontCare $ tag2 A.Seq DontCare $ tag2 A.Several DontCare ([] :: [A.Structured]))
      ) (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
    ]
   )
   
  ,pass ("function uint8: f(uint8: x) {}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 101" $ tag2 A.Several DontCare [tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "f") $
        tag5 A.Function DontCare A.PlainSpec [A.Byte] [tag3 A.Formal A.ValAbbrev A.Byte (simpleNamePattern "x")] $
          (tag2 A.OnlyP DontCare $ tag2 A.Seq DontCare $ tag2 A.Several DontCare ([] :: [A.Structured]))
      ) (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
    ]	
   )   

  ,pass ("function uint8: id(uint8: x) {return x;}", RP.topLevelDecl,
    assertPatternMatch "testTopLevelDecl 101" $ tag2 A.Several DontCare [tag3 A.Spec DontCare
      (tag3 A.Specification DontCare (simpleNamePattern "id") $
        tag5 A.Function DontCare A.PlainSpec [A.Byte] [tag3 A.Formal A.ValAbbrev A.Byte (simpleNamePattern "x")] $
          (tag2 A.OnlyP DontCare $ tag2 A.Seq DontCare $ tag2 A.Several DontCare [tag2 A.OnlyEL DontCare $ tag2 A.ExpressionList DontCare [exprVariablePattern "x"]])
      ) (tag2 A.OnlyP DontCare $ tag1 A.Main DontCare)
    ]
   )
 ]

nonShared :: A.ChanAttributes
nonShared = A.ChanAttributes { A.caWritingShared = False, A.caReadingShared = False}

testDataType :: [ParseTest A.Type]
testDataType =
 [
  pass ("bool",RP.dataType,assertEqual "testDataType 0" A.Bool)
  ,pass ("int",RP.dataType,assertEqual "testDataType 1" A.Int)
  ,pass ("uint8",RP.dataType,assertEqual "testDataType 2" A.Byte)
  ,pass ("uint16",RP.dataType,assertEqual "testDataType 3" A.UInt16)
  ,pass ("uint32",RP.dataType,assertEqual "testDataType 4" A.UInt32)
  ,pass ("uint64",RP.dataType,assertEqual "testDataType 5" A.UInt64)
  ,pass ("sint8",RP.dataType,assertEqual "testDataType 6" A.Int8)
  ,pass ("sint16",RP.dataType,assertEqual "testDataType 7" A.Int16)
  ,pass ("sint32",RP.dataType,assertEqual "testDataType 8" A.Int32)
  ,pass ("sint64",RP.dataType,assertEqual "testDataType 9" A.Int64)
  ,pass ("boolean",RP.dataType,assertEqual "testDataType 10" $ A.UserDataType $ typeName "boolean")
  ,pass ("uint24",RP.dataType,assertEqual "testDataType 11" $ A.UserDataType $ typeName "uint24")
  ,pass ("int0",RP.dataType,assertEqual "testDataType 12" $ A.UserDataType $ typeName "int0")
  ,fail ("bool bool",RP.dataType)
  
  ,pass ("?int",RP.dataType,assertEqual "testDataType 102" $ A.Chan A.DirInput nonShared A.Int)
  ,pass ("! bool",RP.dataType,assertEqual "testDataType 103" $ A.Chan A.DirOutput nonShared A.Bool)
  --These types should succeed in the *parser* -- they would be thrown out further down the line:
  ,pass ("??int",RP.dataType,assertEqual "testDataType 104" $ A.Chan A.DirInput nonShared $ A.Chan A.DirInput nonShared A.Int)
  ,pass ("? ? int",RP.dataType,assertEqual "testDataType 105" $ A.Chan A.DirInput nonShared $ A.Chan A.DirInput nonShared A.Int)
  ,pass ("!!bool",RP.dataType,assertEqual "testDataType 106" $ A.Chan A.DirOutput nonShared $ A.Chan A.DirOutput nonShared A.Bool)
  ,pass ("?!bool",RP.dataType,assertEqual "testDataType 107" $ A.Chan A.DirInput nonShared $ A.Chan A.DirOutput nonShared A.Bool)
  
  ,fail ("?",RP.dataType)
  ,fail ("!",RP.dataType)
  ,fail ("??",RP.dataType)
  ,fail ("int?",RP.dataType)
  ,fail ("bool!",RP.dataType)
  ,fail ("int?int",RP.dataType)  
  
  ,pass ("channel bool",RP.dataType,assertEqual "testDataType 200" $ A.Chan A.DirUnknown nonShared A.Bool)
 ]
 
testDecl :: [ParseTest (Meta, A.Structured -> A.Structured)]
testDecl =
 [
  passd ("bool: b;",0,tag3 A.Specification DontCare (simpleNamePattern "b") $ tag2 A.Declaration DontCare A.Bool)
  ,passd ("uint8: x;",1,tag3 A.Specification DontCare (simpleNamePattern "x") $ tag2 A.Declaration DontCare A.Byte)
  ,passd ("?bool: bc;",2,tag3 A.Specification DontCare (simpleNamePattern "bc") $ tag2 A.Declaration DontCare $ A.Chan A.DirInput nonShared A.Bool)
  ,passd ("a: b;",3,tag3 A.Specification DontCare (simpleNamePattern "b") $ tag2 A.Declaration DontCare (tag1 A.UserDataType $ tag3 A.Name DontCare A.DataTypeName "a"))

  ,passd2 ("bool: b0,b1;",100,tag3 A.Specification DontCare (simpleNamePattern "b0") $ tag2 A.Declaration DontCare A.Bool,
                                tag3 A.Specification DontCare (simpleNamePattern "b1") $ tag2 A.Declaration DontCare A.Bool)
  
  
  ,fail ("bool:;",RP.declaration)
  ,fail ("bool;",RP.declaration)
  ,fail (":b;",RP.declaration)
  ,fail ("bool:b",RP.declaration)
  ,fail ("bool b",RP.declaration)
  ,fail ("bool b;",RP.declaration)
  ,fail ("bool:?b;",RP.declaration)
  ,fail ("bool:b,;",RP.declaration)
  ,fail ("bool: b0 b1;",RP.declaration)
 ]
 where
   passd :: (String,Int,Pattern) -> ParseTest (Meta, A.Structured -> A.Structured)
   passd (code,index,exp) = pass(code,RP.declaration,check ("testDecl " ++ (show index)) exp)
   check :: String -> Pattern -> (Meta, A.Structured -> A.Structured) -> Assertion
   check msg spec (_,act) = assertPatternMatch msg (tag3 A.Spec DontCare spec $ A.Several m []) (act $ A.Several m [])

   passd2 :: (String,Int,Pattern,Pattern) -> ParseTest (Meta, A.Structured -> A.Structured)
   passd2 (code,index,expOuter,expInner) = pass(code,RP.declaration,check2 ("testDecl " ++ (show index)) expOuter expInner)
   check2 :: String -> Pattern -> Pattern -> (Meta, A.Structured -> A.Structured) -> Assertion
   check2 msg specOuter specInner (_,act) = assertPatternMatch msg (tag3 A.Spec DontCare specOuter $ tag3 A.Spec DontCare specInner $ A.Several m []) (act $ A.Several m [])

testComm :: [ParseTest A.Process]
testComm =
 [
  --Output:
  pass ("c ! x;",RP.statement,assertEqual "testComm 0" $ A.Output m (variable "c") [A.OutExpression m (exprVariable "x")])
  ,pass ("c!x;",RP.statement,assertEqual "testComm 1" $ A.Output m (variable "c") [A.OutExpression m (exprVariable "x")])
  ,pass ("c!0+x;",RP.statement,assertEqual "testComm 2" $ A.Output m (variable "c") [A.OutExpression m $ A.Dyadic m A.Plus (intLiteral 0) (exprVariable "x")])
  ,pass ("c!!x;",RP.statement,assertEqual "testComm 3" $ A.Output m (variable "c") [A.OutExpression m $ (exprDirVariable A.DirOutput "x")])
  ,fail ("c!x",RP.statement)
  ,fail ("c!x!y;",RP.statement)  
  ,fail ("c!x,y;",RP.statement)
  ,fail ("c!;",RP.statement)
  ,fail ("!x;",RP.statement)

  --Input:
  ,pass ("c ? x;",RP.statement, assertEqual "testComm 100" $ A.Input m (variable "c") $ A.InputSimple m [A.InVariable m (variable "x")])
  ,pass ("c?x;",RP.statement, assertEqual "testComm 101" $ A.Input m (variable "c") $ A.InputSimple m [A.InVariable m (variable "x")])
  --Later will probably become the extended rendezvous syntax:
  ,pass ("c??x;",RP.statement, assertEqual "testComm 101" $ A.Input m (variable "c") $ A.InputSimple m [A.InVariable m (A.DirectedVariable m A.DirInput $ variable "x")])
  ,fail ("c ? x + 0;",RP.statement)
  ,fail ("?x;",RP.statement)
  ,fail ("c ? x",RP.statement)
  ,fail ("c ? ;",RP.statement)
  ,fail ("c ? x ? y;",RP.statement)
  ,fail ("c ? x , y;",RP.statement)  
 ]

testRun :: [ParseTest A.Process]
testRun =
 [
  pass ("run foo();",RP.statement,assertPatternMatch "testRun 1" $ tag3 A.ProcCall DontCare (procNamePattern "foo") ([] :: [A.Actual]))
  ,pass ("run foo(c);",RP.statement,assertPatternMatch "testRun 2" $ tag3 A.ProcCall DontCare (procNamePattern "foo") 
    [tag3 A.ActualVariable A.Original A.Any (variablePattern "c")])
  ,pass ("run foo(c,0+x);",RP.statement,assertPatternMatch "testRun 3" $ tag3 A.ProcCall DontCare (procNamePattern "foo")
    [tag3 A.ActualVariable A.Original A.Any (variablePattern "c"),tag2 A.ActualExpression A.Any $ tag4 A.Dyadic DontCare A.Plus (intLiteralPattern 0) (exprVariablePattern "x")])  
  ,fail ("run",RP.statement)
  ,fail ("run;",RP.statement)
  ,fail ("run ();",RP.statement)
  ,fail ("run foo()",RP.statement)
  ,fail ("run foo(,);",RP.statement)
  
 ]
        
--Returns the list of tests:
tests :: Test
tests = TestList
 [
  parseTests testExprs,
  parseTests testLiteral,
  parseTests testRange,
  parseTests testWhile,
  parseTests testSeq,
  parseTests testPar,
  parseTests testBlock,
  parseTests testEach,
  parseTests testIf,
  parseTests testAssign,
  parseTests testDataType,
  parseTests testComm,
  parseTests testRun,
  parseTests testDecl,
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

