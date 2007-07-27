module RainParseTest () where

import qualified RainParse as RP
import qualified AST as A
import Text.ParserCombinators.Parsec (runParser,eof)
import Test.HUnit
import Metadata (Meta,emptyMeta)
import Prelude hiding (fail)

data ParseTest a = Show a => ExpPass (String, RP.RainParser a , (a -> Assertion)) | ExpFail (String, RP.RainParser a)

pass :: Show a => (String, RP.RainParser a , (a -> Assertion)) -> ParseTest a
pass x = ExpPass x

fail :: Show a => (String, RP.RainParser a) -> ParseTest a
fail x = ExpFail x

--TODO must make sure that the whole input is consumed?  (is this needed?)

--Runs a parse test, given a tuple of: (source text, parser function, assert)
testParsePass :: Show a => (String, RP.RainParser a , (a -> Assertion)) -> Assertion
testParsePass (text,prod,test)
    = case (runParser parser RP.emptyState "" text) of
        Left error -> assertString (show error)
        Right result -> ((return result) >>= test)
    where parser = do { p <- prod ; eof ; return p}

testParseFail :: Show a => (String, RP.RainParser a) -> Assertion
testParseFail (text,prod)
    = case (runParser parser RP.emptyState "" text) of
        Left error -> return ()
        Right result -> assertFailure ("Test was expected to fail:\n***BEGIN CODE***\n" ++ text ++ "\n*** END CODE ***\n")
    where parser = do { p <- prod ; eof ; return p}

m :: Meta
m = emptyMeta

--Helper function for creating an A.Name object:
simpleName :: String -> A.Name
simpleName s = A.Name { A.nameName = s , A.nameMeta = emptyMeta , A.nameType = A.VariableName }

--Helper function for creating a simple variable name as an expression:
exprVariable :: String -> A.Expression
exprVariable e = A.ExprVariable emptyMeta $ A.Variable emptyMeta $ simpleName e

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

makeSimpleAssign :: String -> String -> A.Process
makeSimpleAssign dest src = A.Assign m [A.Variable m $ simpleName dest] (A.ExpressionList m [exprVariable src])

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
        
--Returns the list of tests:
testList :: [Test]
testList = 
 [
  parseTest testExp0,parseTest testExp1,
  parseTests testWhile,
  parseTests testSeq,
  parseTests testPar,
  parseTests testIf,
  parseTests testAssign
 ]

  where
    parseTest :: Show a => ParseTest a -> Test
    parseTest (ExpPass test) = TestCase (testParsePass test)
    parseTest (ExpFail test) = TestCase (testParseFail test)
    parseTests :: Show a => [ParseTest a] -> Test
    parseTests tests = TestList (map parseTest tests)

    
--Main function; runs the tests
main :: IO ()
main = do runTestTT $ TestList testList
          return ()
