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

-- #ignore-exports

-- | Tests for the C and C++ backends
module GenerateCTest (tests) where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Writer
import Data.List (isInfixOf, intersperse)
import Data.Maybe (fromMaybe)
import Test.HUnit hiding (State)
import Text.Regex

import qualified AST as A
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import Metadata
import Pattern
import TestUtil
import TreeUtil

at :: CGen ()
at = tell ["@"]

dollar :: CGen ()
dollar = tell ["$"]

caret :: CGen ()
caret = tell ["^"]

foo :: A.Name
foo = simpleName "foo"

bar:: A.Name
bar = simpleName "bar"

-- | Asserts that the given output of a CGen pass matches the expected value.
assertGen :: String -> String -> IO (Either Errors.ErrorReport [String]) -> Assertion
assertGen n exp act
      = do r <- act 
           case r of 
             Left (_,err) -> assertFailure $ n ++ " pass failed, error: " ++ err
             Right ss -> assertEqual n exp (subRegex (mkRegex "/\\*\\*/") (concat ss) "")

-- | Asserts that the given output of a CGen pass matches the expected regex
assertGenR :: String -> String -> IO (Either Errors.ErrorReport [String]) -> IO [String]
assertGenR n exp act
      = do r <- act 
           case r of 
             Left (_,err) -> (assertFailure $ n ++ " pass failed, error: " ++ err) >> return []
             Right ss ->
               case matchRegex (mkRegex exp) (subRegex (mkRegex "/\\*\\*/") (concat ss) "") of
                 Just matches -> return matches
                 Nothing -> (assertFailure $ n ++ " regex match failed, regex: \"" ++ exp ++ "\" text: " ++ (concat ss)) >> return []


-- | Asserts that the given output of a CGen pass is a failure
assertGenFail :: String -> IO (Either Errors.ErrorReport [String]) -> Assertion
assertGenFail n act
      = do r <- act 
           case r of 
             Left _ -> return ()
             Right ss -> if isInfixOf "#error" (concat ss)
                           then return ()
                           else assertFailure $ n ++ " pass succeeded when expected to fail, output: " ++ (subRegex (mkRegex "/\\*\\*/") (concat ss) "")


testBothS :: 
  String -- ^ Test Name
  -> String -- ^ C expected
  -> String -- ^ C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> (State CompState ()) -- ^ State transformation  
  -> Test
  
testBothS testName expC expCPP act startState = TestList
   [TestCase $ assertGen (testName ++ "/C") expC $ (evalStateT (runErrorT (execWriterT $ act cgenOps)) state) 
   ,TestCase $ assertGen (testName ++ "/C++") expCPP $ (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state) ]
  where
    state = execState startState emptyState

testBothFailS :: String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testBothFailS testName act startState = TestList
   [TestCase $ assertGenFail (testName ++ "/C") (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
   ,TestCase $ assertGenFail (testName ++ "/C++") (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state) ]
  where
    state = execState startState emptyState

testRS :: String -> String -> CGen () -> State CompState () -> IO [String]
testRS testName exp act startState = assertGenR testName exp (evalStateT (runErrorT (execWriterT act)) state)
  where
    state = execState startState emptyState

-- Tests C output, expects C++ to fail
testCFS :: String -> String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testCFS testName expC act startState = TestCase $
  do assertGen (testName ++ "/C") expC $ (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGenFail (testName ++ "/C++") (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState
    
-- Tests C++ output, expects C to fail
testCPPFS :: String -> String -> (GenOps -> CGen ()) -> (State CompState ()) -> Test
testCPPFS testName expCPP act startState = TestCase $
  do assertGenFail (testName ++ "/C") (evalStateT (runErrorT (execWriterT $ act cgenOps)) state)
     assertGen (testName ++ "/C++") expCPP $ (evalStateT (runErrorT (execWriterT $ act cppgenOps)) state)
  where
    state = execState startState emptyState    

testBothSameS :: 
  String    -- ^ Test Name
  -> String -- ^ C and C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> (State CompState ()) -- ^ State transformation
  -> Test
testBothSameS n e a s = testBothS n e e a s

testBothSameR :: 
  String    -- ^ Test Name
  -> String -- ^ C and C++ expected
  -> (GenOps -> CGen ()) -- ^ Actual
  -> Test
testBothSameR n e a = TestCase $ (testRS n e (a cgenOps) (return ())) >> (testRS n e (a cppgenOps) (return ())) >> (return ())

testBothFail :: String -> (GenOps -> CGen ()) -> Test
testBothFail a b = testBothFailS a b (return ())
  
testBoth :: String -> String -> String -> (GenOps -> CGen ()) -> Test
testBoth a b c d = testBothS a b c d (return ())

testBothSame :: String -> String -> (GenOps -> CGen ()) -> Test
testBothSame a b c = testBothSameS a b c (return ())
  
testCF :: String -> String -> (GenOps -> CGen ()) -> Test
testCF a b c = testCFS a b c (return ())

testCPPF :: String -> String -> (GenOps -> CGen ()) -> Test
testCPPF a b c = testCPPFS a b c (return ())
  
tcall :: (GenOps -> GenOps -> a -> b) -> a -> (GenOps -> b)
tcall f x = (\o -> f o o x)

tcall2 :: (GenOps -> GenOps -> a0 -> a1 -> b) -> a0 -> a1 -> (GenOps -> b)
tcall2 f x y = (\o -> f o o x y)

tcall3 :: (GenOps -> GenOps -> a0 -> a1 -> a2 -> b) -> a0 -> a1 -> a2 -> (GenOps -> b)
tcall3 f x y z = (\o -> f o o x y z)

-- | Overrides a specified function in GenOps to return the given value
override1 ::
  b -- ^ The value to return for the overridden function
  -> (GenOps -> a -> b) -- ^ The resulting overriden function
override1 val = (\_ _ -> val)

override2 :: b -> (GenOps -> a0 -> a1 -> b)
override2 val = (\_ _ _ -> val)

override3 :: b -> (GenOps -> a0 -> a1 -> a2 -> b)
override3 val = (\_ _ _ _ -> val)

testGenType :: Test
testGenType = TestList 
 [
  testBothSame "GenType 0" "uint8_t" (tcall genType A.Byte) 
  ,testBothSame "GenType 1" "uint16_t" (tcall genType A.UInt16) 
  ,testBothSame "GenType 2" "uint32_t" (tcall genType A.UInt32) 
  ,testBothSame "GenType 3" "uint64_t" (tcall genType A.UInt64) 
  ,testBothSame "GenType 4" "int8_t" (tcall genType A.Int8) 
  ,testBothSame "GenType 5" "int16_t" (tcall genType A.Int16) 
  ,testBothSame "GenType 6" "int32_t" (tcall genType A.Int32) 
  ,testBothSame "GenType 7" "int64_t" (tcall genType A.Int64) 
  ,testBothSame "GenType 8" "int" (tcall genType A.Int) 
  ,testBoth "GenType 9" "bool" "tockBool" (tcall genType A.Bool) 
  ,testBothSame "GenType 10" "float" (tcall genType A.Real32) 
  ,testBothSame "GenType 11" "double" (tcall genType A.Real64) 
  ,testBoth "GenType 100" "int*" "tockArrayView<int,1>" (tcall genType $ A.Array [A.Dimension 5] A.Int) 
  ,testBoth "GenType 101" "int*" "tockArrayView<int,3>" (tcall genType $ A.Array [A.Dimension 5, A.Dimension 2, A.Dimension 9] A.Int) 
  ,testBoth "GenType 102" "int*" "tockArrayView<int,2>" (tcall genType $ A.Array [A.Dimension 5, A.UnknownDimension] A.Int) 
  ,testBothSame "GenType 103" "foo" (tcall genType $ A.Record (simpleName "foo")) 
  ,testBoth "GenType 200" "Time" "csp::Time" (tcall genType A.Time) 
  ,testBoth "GenType 201" "Time" "csp::Time" (tcall genType A.Timer) 

  ,testBoth "GenType 300" "Channel" "csp::One2OneChannel<int>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int) 
  ,testBoth "GenType 301" "Channel" "csp::One2AnyChannel<int>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False True) A.Int) 
  ,testBoth "GenType 302" "Channel" "csp::Any2OneChannel<int>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True False) A.Int) 
  ,testBoth "GenType 303" "Channel" "csp::Any2AnyChannel<int>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True True) A.Int) 
  
  ,testBoth "GenType 400" "Channel*" "csp::Chanin<int>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int) 
  ,testBoth "GenType 401" "Channel*" "csp::Chanin<int>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False True) A.Int) 

  ,testBoth "GenType 402" "Channel*" "csp::Chanout<int>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes False False) A.Int) 
  ,testBoth "GenType 403" "Channel*" "csp::Chanout<int>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes True False) A.Int) 
  
  --ANY and protocols can occur outside channels in C++ (e.g. temporaries for reading from channels), so they are tested here:
  ,testCPPF "GenType 500" "tockAny" (tcall genType $ A.Any) 
  ,testCPPF "GenType 600" "protocol_foo" (tcall genType $ A.UserProtocol (simpleName "foo")) 
  
  ,testBoth "GenType 700" "Channel*" "tockArrayView<csp::One2OneChannel<int>,1>" (tcall genType $ A.Array [A.Dimension 5] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testBoth "GenType 701" "Channel**" "tockArrayView<csp::Chanin<int>,1>" (tcall genType $ A.Array [A.Dimension 5] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
 ]

testStop :: Test
testStop =
  testBoth "Stop" "occam_stop(\"foo:4:9\",\"bar\");" "throw StopException(\"foo:4:9\" \"bar\");" (tcall2 genStop (Meta (Just "foo") 4 9) "bar") 

testArraySizes :: Test
testArraySizes = TestList
 [
  testBothSame "genArraySizesLiteral 0" "3" (tcall genArraySizesLiteral [A.Dimension 3]) 
  ,testBothSame "genArraySizesLiteral 1" "3,6,8" (tcall genArraySizesLiteral [A.Dimension 3, A.Dimension 6, A.Dimension 8]) 
  ,testBothFail "genArraySizesLiteral 2" (tcall genArraySizesLiteral [A.Dimension 6, A.UnknownDimension]) 
  ,testBothSame "genArraySizesSize 0" "[1]" (tcall genArraySizesSize [A.Dimension 7])
  ,testBothSame "genArraySize 0" "const int*foo_sizes=@;" (tcall3 genArraySize True at foo)
  ,testBothSame "genArraySize 1" "const int foo_sizes[]={@};" (tcall3 genArraySize False at foo)
  ,testBothSame "genArrayLiteralElems 0" "$" $ (tcall genArrayLiteralElems [A.ArrayElemExpr undefined]) . unfolded
  ,testBothSame "genArrayLiteralElems 1" "$,$,$" $ (tcall genArrayLiteralElems [A.ArrayElemExpr undefined, A.ArrayElemExpr undefined, A.ArrayElemExpr undefined]) . unfolded
  ,testBothSame "genArrayLiteralElems 2" "$,$,$" $ (tcall genArrayLiteralElems [A.ArrayElemExpr undefined, A.ArrayElemArray [A.ArrayElemExpr undefined, A.ArrayElemExpr undefined]]) . unfolded
 ]
 where
  unfolded = (\ops -> ops {genUnfoldedExpression = override1 dollar})

testActuals :: Test
testActuals = TestList
 [
  -- C adds a prefix comma (to follow Process* me) but C++ does not:
  testBoth "genActuals 0" ",@,@" "@,@" $ (tcall genActuals [undefined, undefined]) . (\ops -> ops {genActual = override1 at})
  ,testBothSame "genActuals 1" "" $ (tcall genActuals [])
  
  --For expressions, genExpression should be called:
  ,testBothSame "genActual 0" "$" $ (tcall genActual $ A.ActualExpression A.Bool (A.True undefined)) . over
  
  --For abbreviating arrays, C++ should call genExpression/genVariable, whereas C should do its foo,foo_sizes thing:
  ,testBoth "genActual 1" "@,@_sizes" "$" $ (tcall genActual $ A.ActualExpression (A.Array undefined undefined) (A.ExprVariable undefined $ A.Variable undefined foo)) . over
  ,testBoth "genActual 2" "@,@_sizes" "@" $ (tcall genActual $ A.ActualVariable A.Abbrev (A.Array undefined undefined) (A.Variable undefined foo)) . over
 ]
 where
   over = (\ops -> ops {genVariable = override1 at, genExpression = override1 dollar})
   
testArraySubscript :: Test
testArraySubscript = TestList
 [
  testBothS "genArraySubscript 0" "[5*foo_sizes[1]*foo_sizes[2]]" "[5]"
    (tcall3 genArraySubscript False (A.Variable emptyMeta foo) [intLiteral 5]) stateTrans
  ,testBothS "genArraySubscript 1" "[5*foo_sizes[1]*foo_sizes[2]+6*foo_sizes[2]]" "[5][6]"
    (tcall3 genArraySubscript False (A.Variable emptyMeta foo) [intLiteral 5, intLiteral 6]) stateTrans
  ,testBothS "genArraySubscript 2" "[5*foo_sizes[1]*foo_sizes[2]+6*foo_sizes[2]+7]" "[5][6][7].access()"
    (tcall3 genArraySubscript False (A.Variable emptyMeta foo) [intLiteral 5, intLiteral 6, intLiteral 7]) stateTrans
  
  ,testBothS "genArraySubscript 3" ("[occam_check_index(5,foo_sizes[0]," ++ m ++ ")*foo_sizes[1]*foo_sizes[2]]") ("[occam_check_index(5,foo.extent(0)," ++ m ++ ")]")
    (tcall3 genArraySubscript True (A.Variable emptyMeta foo) [intLiteral 5]) stateTrans
  ,testBothS "genArraySubscript 4"
    ("[occam_check_index(5,foo_sizes[0]," ++ m ++ ")*foo_sizes[1]*foo_sizes[2]+occam_check_index(6,foo_sizes[1]," ++ m ++ ")*foo_sizes[2]]")
    ("[occam_check_index(5,foo.extent(0)," ++ m ++ ")][occam_check_index(6,foo.extent(1)," ++ m ++ ")]")
    (tcall3 genArraySubscript True (A.Variable emptyMeta foo) [intLiteral 5, intLiteral 6]) stateTrans
  ,testBothS "genArraySubscript 5"
    ("[occam_check_index(5,foo_sizes[0]," ++ m ++ ")*foo_sizes[1]*foo_sizes[2]+occam_check_index(6,foo_sizes[1]," ++ m ++ ")*foo_sizes[2]+occam_check_index(7,foo_sizes[2]," ++ m ++ ")]")
    ("[occam_check_index(5,foo.extent(0)," ++ m ++ ")][occam_check_index(6,foo.extent(1)," ++ m ++ ")][occam_check_index(7,foo.extent(2)," ++ m ++ ")].access()")
    (tcall3 genArraySubscript True (A.Variable emptyMeta foo) [intLiteral 5, intLiteral 6, intLiteral 7]) stateTrans
    
 ]
 where
   stateTrans = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [A.Dimension 7,A.Dimension 8,A.Dimension 8] A.Int)
   m = "\"" ++ show emptyMeta ++ "\""

testOverArray :: Test
testOverArray = TestList $ map testOverArray'
  [(cSize,cIndex,"",cgenOps)
  ,((\n -> "\\.extent\\(" ++ show n ++ "\\)"),cppIndex,"\\.access\\(\\)",cppgenOps)
  ]
  where
    cSize n = "_sizes\\[" ++ show n ++ "\\]"

    cppIndex = concat . (map cppIndex')
    cppIndex' :: (String,[Int]) -> String
    cppIndex' (s,_) = "\\[" ++ s ++ "\\]"

    cIndex x = "\\[" ++ concat (intersperse "\\+" $ map cIndex' x) ++ "\\]"
    cIndex' :: (String,[Int]) -> String
    cIndex' (s,ns) = s ++ concat (map (\n -> "\\*foo" ++ cSize n) ns)

    testOverArray' :: ((Int -> String),[(String,[Int])] -> String,String,GenOps) -> Test
    testOverArray' (sz,f',suff,ops) = TestCase $
      do testRS "testOverArray'" rx1 (tcall3 genOverArray emptyMeta (A.Variable emptyMeta foo) func ops) state1
         testRS "testOverArray'" rx3 (tcall3 genOverArray emptyMeta (A.Variable emptyMeta foo) func ops) state3
         return ()
      where
        func f = Just $ call genVariableUnchecked ops (f $ A.Variable emptyMeta foo) >> tell [";"]
        rx1 = "^for\\(int ([[:alnum:]_]+)=0;\\1<foo" ++ sz 0 ++ ";\\1\\+\\+)\\{foo\\[\\1\\]" ++ suff ++ ";\\}$"
        rx3 = "^for\\(int ([[:alnum:]_]+)=0;\\1<foo" ++ sz 0 ++ ";\\1\\+\\+)\\{" ++
              "for\\(int ([[:alnum:]_]+)=0;\\2<foo" ++ sz 1 ++ ";\\2\\+\\+)\\{" ++
              "for\\(int ([[:alnum:]_]+)=0;\\3<foo" ++ sz 2 ++ ";\\3\\+\\+)\\{" ++
              "foo" ++ (f' [("\\1",[1,2]),("\\2",[2]),("\\3",[])]) ++ suff ++ ";\\}\\}\\}$"
        state1 = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [A.Dimension 7] A.Int)
        state3 = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [A.Dimension 7, A.Dimension 8, A.Dimension 9] A.Int)

testReplicator :: Test
testReplicator = TestList
 [
  testBothSame "testReplicator 0" "for(int foo=0;foo<10;foo++){@}" (tcall2 genReplicator (A.For emptyMeta foo (intLiteral 0) (intLiteral 10)) at)
  ,testBothSameR "testReplicator 1" "for\\(int ([[:alnum:]_]+)=10,foo=1;\\1>0;\\1--,foo\\+\\+\\)\\{@\\}" (tcall2 genReplicator (A.For emptyMeta foo (intLiteral 1) (intLiteral 10)) at)
 ]

testDeclaration :: Test
testDeclaration = TestList
 [
  --Simple: 
  testBothSame "genDeclaration 0" "int foo;" (tcall2 genDeclaration A.Int foo)
  
  --Channels and channel-ends:
  ,testBoth "genDeclaration 1" "Channel foo;" "csp::One2OneChannel<int> foo;" (tcall2 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int) foo)
  ,testBoth "genDeclaration 2" "Channel foo;" "csp::Any2OneChannel<int> foo;" (tcall2 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes True False) A.Int) foo)
  ,testBoth "genDeclaration 3" "Channel foo;" "csp::One2AnyChannel<int> foo;" (tcall2 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes False True) A.Int) foo)
  ,testBoth "genDeclaration 4" "Channel foo;" "csp::Any2AnyChannel<int> foo;" (tcall2 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes True True) A.Int) foo)
  ,testBoth "genDeclaration 5" "Channel* foo;" "csp::Chanin<int> foo;" (tcall2 genDeclaration (A.Chan A.DirInput (A.ChanAttributes False False) A.Int) foo)
  ,testBoth "genDeclaration 6" "Channel* foo;" "csp::Chanin<int> foo;" (tcall2 genDeclaration (A.Chan A.DirInput (A.ChanAttributes False True) A.Int) foo)
  ,testBoth "genDeclaration 7" "Channel* foo;" "csp::Chanout<int> foo;" (tcall2 genDeclaration (A.Chan A.DirOutput (A.ChanAttributes False False) A.Int) foo)
  ,testBoth "genDeclaration 8" "Channel* foo;" "csp::Chanout<int> foo;" (tcall2 genDeclaration (A.Chan A.DirOutput (A.ChanAttributes True False) A.Int) foo)  
  
  --Arrays (of simple):
  ,testBoth "genDeclaration 100" "int foo[8];const int foo_sizes[]={8};" "int foo_actual[8];tockArrayView<int,1> foo(foo_actual,tockDims(8));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8] A.Int) foo)
  ,testBoth "genDeclaration 101" "int foo[8*9];const int foo_sizes[]={8,9};" "int foo_actual[8*9];tockArrayView<int,2> foo(foo_actual,tockDims(8,9));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8,A.Dimension 9] A.Int) foo)
  ,testBoth "genDeclaration 102" "int foo[8*9*10];const int foo_sizes[]={8,9,10};" "int foo_actual[8*9*10];tockArrayView<int,3> foo(foo_actual,tockDims(8,9,10));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8,A.Dimension 9,A.Dimension 10] A.Int) foo)
  
  --Arrays of channels and channel-ends:
  ,testBoth "genDeclaration 200" "Channel foo[8];const int foo_sizes[]={8};"
    "csp::One2OneChannel<int> foo_actual[8];tockArrayView<csp::One2OneChannel<int>,1> foo(foo_actual,tockDims(8));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int) foo)

  ,testBoth "genDeclaration 201" "Channel foo[8*9];const int foo_sizes[]={8,9};"
    "csp::One2OneChannel<int> foo_actual[8*9];tockArrayView<csp::One2OneChannel<int>,2> foo(foo_actual,tockDims(8,9));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8, A.Dimension 9] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int) foo)
    
  ,testBoth "genDeclaration 202" "Channel* foo[8];const int foo_sizes[]={8};"
    "csp::Chanin<int> foo_actual[8];tockArrayView<csp::Chanin<int>,1> foo(foo_actual,tockDims(8));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int) foo)

  ,testBoth "genDeclaration 203" "Channel* foo[8*9];const int foo_sizes[]={8,9};"
    "csp::Chanout<int> foo_actual[8*9];tockArrayView<csp::Chanout<int>,2> foo(foo_actual,tockDims(8,9));"
    (tcall2 genDeclaration (A.Array [A.Dimension 8, A.Dimension 9] $ A.Chan A.DirOutput (A.ChanAttributes False False) A.Int) foo)
 ]
 

testDeclareInitFree :: Test
testDeclareInitFree = TestList
 [
  testAllSame 0 ("","") A.Int
  ,testAll 1 ("ChanInit((&foo));","") ("","") $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int
  ,testAllSame 2 ("","") $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int
  ,testAllSame 3 ("","") $ A.Array [A.Dimension 4] A.Int
  ,testAll 4 ("^ChanInit((&foo[0]));^","") ("","") $ A.Array [A.Dimension 4] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int
  ,testAllSame 5 ("","") $ A.Array [A.Dimension 4] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int
 ]
 where
   testAll :: Int -> (String,String) -> (String,String) -> A.Type -> Test
   testAll n (iC,fC) (iCPP,fCPP) t = TestList
    [
     testBothS ("testDeclareInitFree/a" ++ show n) ("@" ++ iC) ("@" ++ iCPP) ((tcall introduceSpec $ A.Specification emptyMeta foo (A.Declaration emptyMeta t)) . over) state
     ,testBothS ("testDeclareInitFree/b" ++ show n) iC iCPP ((fromMaybe (return ())) . (tcall3 declareInit emptyMeta t (A.Variable emptyMeta foo)) . over) state
     ,testBothS ("testDeclareInitFree/c" ++ show n) fC fCPP ((tcall removeSpec $ A.Specification emptyMeta foo (A.Declaration emptyMeta t)) . over) state
     ,testBothS ("testDeclareInitFree/d" ++ show n) fC fCPP ((fromMaybe (return ())) . (tcall3 declareFree emptyMeta t (A.Variable emptyMeta foo)) . over) state
    ]
     where
       overArray _ _ v f = case f (\v -> A.SubscriptedVariable emptyMeta (A.Subscript emptyMeta $ intLiteral 0) v) of
         Just p -> caret >> p >> caret
         Nothing -> return ()
       over ops = ops {genDeclaration = override2 at, genOverArray = overArray}
       state = defineName (simpleName "foo") $ simpleDefDecl "foo" t
   testAllSame :: Int -> (String,String) -> A.Type -> Test
   testAllSame n e t = testAll n e e t

defRecord :: String -> String -> A.Type -> State CompState ()
defRecord rec mem t = defineName (simpleName rec) $ A.NameDef emptyMeta rec rec A.RecordName (A.RecordType emptyMeta False [(simpleName mem,t)]) A.Original A.Unplaced

testGenVariable :: Test
testGenVariable = TestList
 [
  -- Various types, unsubscripted:
  testSameA 0 ("foo","(*foo)","foo") id A.Int
  ,testSameA 10 ("(&foo)","foo","foo") id (A.Record bar)
  ,testSameA2 20 ("(&foo)","foo") id (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testSameA2 30 ("foo","foo") id (A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
  
  -- Arrays of the previous types, unsubscripted:
  ,testSameA 100 ("foo","foo","foo") id (A.Array [A.Dimension 8] A.Int)
  ,testSameA 110 ("foo","foo","foo") id (A.Array [A.Dimension 8] $ A.Record bar)
  ,testSameA2 120 ("foo","foo") id (A.Array [A.Dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testSameA2 130 ("foo","foo") id (A.Array [A.Dimension 8] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
  
  -- Subscripted record:
  ,testSameA 200 ("(&foo)->x","foo->x","foo->x") fieldX (A.Record bar)
  
  -- Fully subscripted array:
  ,testAC 300 ("foo@C4","foo@U4") (sub 4) (A.Array [A.Dimension 8] A.Int)
  ,testAC 305 ("foo@C4,5,6","foo@U4,5,6") ((sub 6) . (sub 5) . (sub 4)) (A.Array [A.Dimension 8,A.Dimension 9,A.Dimension 10] A.Int)
  ,testAC 310 ("(&foo@C4)","(&foo@U4)") (sub 4) (A.Array [A.Dimension 8] $ A.Record bar)
  ,testAC 320 ("(&foo@C4)","(&foo@U4)") (sub 4) (A.Array [A.Dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testAC 330 ("foo@C4","foo@U4") (sub 4) (A.Array [A.Dimension 8] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
  
  -- Fully subscripted array, and record field reference:
  ,testAC 400 ("(&foo@C4)->x","(&foo@U4)->x") (fieldX . (sub 4)) (A.Array [A.Dimension 8] $ A.Record bar)
  -- As above, but then with an index too:
  ,testAC 410 ("(&foo@C4)->x@C4","(&foo@U4)->x@U4") ((sub 4) . fieldX . (sub 4)) (A.Array [A.Dimension 8] $ A.Record bar)
  
  --TODO come back to slices later
 ]
 where
   fieldX = A.SubscriptedVariable emptyMeta (A.SubscriptField emptyMeta $ simpleName "x")
   sub n = A.SubscriptedVariable emptyMeta (A.Subscript emptyMeta $ intLiteral n)
 
   test :: Int -> (String,String) -> (String,String) -> (A.Variable -> A.Variable) -> A.AbbrevMode -> A.Type -> Test
   test n (eC,eUC) (eCPP,eUCPP) sub am t = TestList
    [
     testBothS ("testGenVariable/checked" ++ show n) eC eCPP ((tcall genVariable $ sub $ A.Variable emptyMeta foo) . over) state
     ,testBothS ("testGenVariable/unchecked" ++ show n) eUC eUCPP ((tcall genVariableUnchecked $ sub $ A.Variable emptyMeta foo) . over) state
    ]
     where
       state = do defineName (simpleName "foo") $ A.NameDef emptyMeta "foo" "foo" A.VariableName (A.Declaration emptyMeta t) am A.Unplaced
                  defRecord "bar" "x" $ A.Array [A.Dimension 7] A.Int
       over ops = ops {genArraySubscript = (\_ b _ subs -> at >> (tell [if b then "C" else "U"]) >> (seqComma $ map (call genExpression ops) subs))}
   
   testA :: Int -> (String,String) -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testA n eC eCPP sub t = TestList [test n eC eCPP sub A.Original t, test (n+1) eC eCPP sub A.Abbrev t, test (n+2) eC eCPP sub A.ValAbbrev t]
   
   testAC :: Int -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testAC n e sub t = testA n e e sub t
   
   
   testSame :: Int -> String -> (A.Variable -> A.Variable) -> A.AbbrevMode -> A.Type -> Test
   testSame n e sub am t = test n (e,e) (e,e) sub am t
   
   testSameA :: Int -> (String,String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testSameA n (eO,eA,eVA) sub t = TestList [testSame n eO sub A.Original t,testSame (n+1) eA sub A.Abbrev t,testSame (n+2) eVA sub A.ValAbbrev t]

   testSameA2 :: Int -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testSameA2 n (eO,eA) sub t = TestList [testSame n eO sub A.Original t,testSame (n+1) eA sub A.Abbrev t]

---Returns the list of tests:
tests :: Test
tests = TestList
 [
   testActuals
   ,testArraySizes
   ,testArraySubscript
   ,testDeclaration
   ,testDeclareInitFree
   ,testGenType
   ,testGenVariable
   ,testOverArray
   ,testReplicator
   ,testStop
 ]
