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
--
-- The testing strategy is as follows.  The way we have implemented the C and C++ backends is 
-- to have a dictionary of functions 'GenerateC.GenOps' that is used for (mutually) recursive
-- calls.  We can take advantage of this during testing.  For example, we have a test that
-- tests genArraySubscript directly.  When we test genVariableChecked, we don't want to have
-- to effectively check parts of genArraySubscript again.  So we can \"override\" the
-- genArraySubscript to return a dummy value, and then we are effectively testing 
-- that genVariableChecked calls genArraySubscript at the appropriate point.  This is similar
-- to a testing technique in OOP where one might take a class and override some methods to
-- do a similar trick.
module GenerateCTest (tests) where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer hiding (tell)
import Data.Generics
import Data.List (isInfixOf, intersperse)
import Data.Maybe (fromMaybe)
import Test.HUnit hiding (State)
import Text.Regex

import qualified AST as A
import CompState
import Errors
import GenerateC
import GenerateCBased
import GenerateCPPCSP
import Metadata
import Pass
import TestUtils
import TypeSizes
import Utils

-- | A few helper functions for writing certain characters (that won't appear in our generated C/C++ source)
-- to the WriterT monad.  Useful as simple placeholders/special values during testers.
at :: CGen ()
at = tell ["@"]

dollar :: CGen ()
dollar = tell ["$"]

caret :: CGen ()
caret = tell ["^"]

hash :: CGen ()
hash = tell ["#"]

backq :: CGen ()
backq = tell ["`"]

-- | A few easy helpers for name variables for testing.
foo :: A.Name
foo = simpleName "foo"

bar:: A.Name
bar = simpleName "bar"

bar2 :: A.Name
bar2 = simpleName "bar2"

-- | Asserts that the given output of a CGen pass matches the expected value.
assertGen :: String -> String -> IO (Either Errors.ErrorReport [String]) -> Assertion
assertGen n exp act
      = do r <- act 
           case r of 
             Left (_,err) -> assertFailure $ n ++ " pass failed, error: " ++ err
             Right ss -> assertEqual n exp (subRegex (mkRegex "/\\*\\*/") (concat ss) "")

-- | Asserts that the given output of a CGen pass matches the expected regex, and returns the matched groups.
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

evalCGen :: CGen () -> GenOps -> CompState -> IO (Either Errors.ErrorReport [String])
evalCGen act ops state = evalCGen' (runReaderT act ops) state

evalCGen' :: CGen' () -> CompState -> IO (Either Errors.ErrorReport [String])
evalCGen' act state = runPassM state pass >>* fst
  where
    pass = execStateT act (Left []) >>* (\(Left x) -> x)

-- | Checks that running the test for the C and C++ backends produces the right output for each.
testBothS :: 
  String -- ^ Test Name
  -> String -- ^ C expected
  -> String -- ^ C++ expected
  -> CGen () -- ^ Actual
  -> (State CompState ()) -- ^ State transformation  
  -> Test
  
testBothS testName expC expCPP act startState = TestList
   [TestCase $ assertGen (testName ++ "/C") expC $ evalCGen act cgenOps state
   ,TestCase $ assertGen (testName ++ "/C++") expCPP $ evalCGen act cppgenOps state]
  where
    state = execState startState emptyState

-- | Checks that both the C and C++ backends fail on the given input.
testBothFailS :: String -> CGen () -> (State CompState ()) -> Test
testBothFailS testName act startState = TestList
   [TestCase $ assertGenFail (testName ++ "/C") (evalCGen act cgenOps state)
   ,TestCase $ assertGenFail (testName ++ "/C++") (evalCGen act cppgenOps state) ]
  where
    state = execState startState emptyState

-- | Checks that the given output of a backend satisfies the given regex, and returns the matched groups.
testRS :: String -> String -> CGen' () -> State CompState () -> IO [String]
testRS testName exp act startState = assertGenR testName exp (evalCGen' act state)
  where
    state = execState startState emptyState

-- | Like testBothS, but with the output of the C and C++ backends the same.
testBothSameS :: 
  String    -- ^ Test Name
  -> String -- ^ C and C++ expected
  -> CGen () -- ^ Actual
  -> (State CompState ()) -- ^ State transformation
  -> Test
testBothSameS n e a s = testBothS n e e a s

-- | Checks that the output of the test matches the given regexes for C and C++
testBothR :: 
  String    -- ^ Test Name
  -> String -- ^ C expected
  -> String -- ^ C++ expected
  -> CGen () -- ^ Actual
  -> Test
testBothR n eC eCPP a = TestList
  [TestCase $ (testRS n eC (runReaderT a cgenOps) (return ())) >> return ()
  ,TestCase $ (testRS n eCPP (runReaderT a cppgenOps) (return ())) >> (return ())]

-- | Like testBothR, but where the output of the C and C++ passes is expected to be the same.
testBothSameR :: String -> String -> CGen () -> Test
testBothSameR n e a = testBothR n e e a

-- | Like testBothFailS, but with the default beginning state.
testBothFail :: String -> CGen () -> Test
testBothFail a b = testBothFailS a b (return ())

-- | Like testBothS, but with the default beginning state.  
testBoth :: String -> String -> String -> CGen () -> Test
testBoth a b c d = testBothS a b c d (return ())

-- | Like testBothSameS, but with the default beginning state.
testBothSame :: String -> String -> CGen () -> Test
testBothSame a b c = testBothSameS a b c (return ())
  
-- | These functions are here for a historical reason, and are all defined
-- to be call.
tcall, tcall2, tcall3, tcall4, tcall5 :: CGenCall a => (GenOps -> a) -> a
tcall = call
tcall2 = call
tcall3 = call
tcall4 = call
tcall5 = call

type Override = CGen () -> CGen ()

-- | Overrides a specified function in GenOps to return the given value
override1 ::
  b -- ^ The value to return for the overridden function
  -> (a -> b) -- ^ The resulting overriden function
override1 val = (\_ -> val)

override2 :: b -> (a0 -> a1 -> b)
override2 val = (\_ _ -> val)

override3 :: b -> (a0 -> a1 -> a2 -> b)
override3 val = (\_ _ _ -> val)

override4 :: b -> (a0 -> a1 -> a2 -> a3 -> b)
override4 val = (\_ _ _ _ -> val)

override5 :: b -> (a0 -> a1 -> a2 -> a3 -> a4 -> b)
override5 val = (\_ _ _ _ _ -> val)

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
  ,testBoth "GenType 8"
    (case cIntSize of
       2 -> "int16_t"
       4 -> "int32_t"
       8 -> "int64_t")
    (case cxxIntSize of
       2 -> "int16_t"
       4 -> "int32_t"
       8 -> "int64_t")
    (tcall genType A.Int)
  ,testBothSame "GenType 9" "bool" (tcall genType A.Bool) 
  ,testBothSame "GenType 10" "float" (tcall genType A.Real32) 
  ,testBothSame "GenType 11" "double" (tcall genType A.Real64) 
  
  ,testBothSame "GenType 20" "uint8_t*" (tcall genType $ A.Mobile A.Byte)
  ,testBothSame "GenType 21" "bool*" (tcall genType $ A.Mobile A.Bool)
  ,testBothSame "GenType 22" "float*" (tcall genType $ A.Mobile A.Real32)
  
  
  ,testBothSame "GenType 100" "int32_t*" (tcall genType $ A.Array [dimension 5] A.Int32) 
  ,testBothSame "GenType 101" "int32_t*" (tcall genType $ A.Array [dimension 5, dimension 2, dimension 9] A.Int32) 
  ,testBothSame "GenType 102" "int32_t*" (tcall genType $ A.Array [dimension 5, A.UnknownDimension] A.Int32) 
  ,testBothSame "GenType 103" "foo" (tcall genType $ A.Record (simpleName "foo")) 
  ,testBoth "GenType 200" "Time" "csp::Time" (tcall genType A.Time) 
  ,testBoth "GenType 201" "Time" "csp::Time" (tcall genType $ A.Timer A.OccamTimer) 
  
  ,testBothSame "GenType 250" "int32_t*" (tcall genType $ A.Mobile $ A.Array [dimension 5, dimension 2, dimension 9] A.Int32) 
  ,testBothSame "GenType 251" "int32_t*" (tcall genType $ A.Mobile $ A.Array [dimension 5, A.UnknownDimension] A.Int32) 
  ,testBothSame "GenType 251" "int32_t*" (tcall genType $ A.Mobile $ A.Array [A.UnknownDimension] A.Int32) 
  ,testBothSame "GenType 252" "foo*" (tcall genType $ A.Mobile $ A.Record (simpleName "foo")) 
  ,testBoth "GenType 253" "Time*" "csp::Time*" (tcall genType $ A.Mobile A.Time)  

  ,testBoth "GenType 300" "Channel" "csp::One2OneChannel<int32_t>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int32) 
  ,testBoth "GenType 301" "Channel" "csp::One2AnyChannel<int32_t>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False True) A.Int32) 
  ,testBoth "GenType 302" "Channel" "csp::Any2OneChannel<int32_t>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True False) A.Int32) 
  ,testBoth "GenType 303" "Channel" "csp::Any2AnyChannel<int32_t>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes True True) A.Int32) 

  ,testBoth "GenType 310" "Channel" "csp::One2OneChannel<int32_t*>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) (A.Mobile A.Int32))
  
  ,testBoth "GenType 400" "Channel*" "csp::Chanin<int32_t>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int32) 
  ,testBoth "GenType 401" "Channel*" "csp::Chanin<int32_t>" (tcall genType $ A.Chan A.DirInput (A.ChanAttributes False True) A.Int32) 

  ,testBoth "GenType 402" "Channel*" "csp::Chanout<int32_t>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes False False) A.Int32) 
  ,testBoth "GenType 403" "Channel*" "csp::Chanout<int32_t>" (tcall genType $ A.Chan A.DirOutput (A.ChanAttributes True False) A.Int32) 
  
  --ANY and protocols cannot occur outside channels in C++ or C, they are tested here:
  ,testBothFail "GenType 500" (tcall genType $ A.Any) 
  ,testBothFail "GenType 600" (tcall genType $ A.UserProtocol (simpleName "foo")) 
  ,testBothFail "GenType 650" (tcall genType $ A.Counted A.Int32 A.Int32) 
   
  ,testBoth "GenType 700" "Channel**" "csp::One2OneChannel<int32_t>**" (tcall genType $ A.Array [dimension 5] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int32)
  ,testBoth "GenType 701" "Channel**" "csp::Chanin<int32_t>*" (tcall genType $ A.Array [dimension 5] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int32)
  
  --Test types that can only occur inside channels:
  --ANY:
  ,testBoth "GenType 800" "Channel" "csp::One2OneChannel<tockSendableArrayOfBytes>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Any)
  --Protocol:
  ,testBoth "GenType 900" "Channel" "csp::One2OneChannel<tockSendableArrayOfBytes>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) $ A.UserProtocol (simpleName "foo"))
  --Counted:
  ,testBoth "GenType 1000" "Channel" "csp::One2OneChannel<tockSendableArrayOfBytes>" (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) $ A.Counted A.Int32 A.Int32)
  
  --Channels of arrays are special in C++:
  ,testBoth "GenType 1100" "Channel" "csp::One2OneChannel<tockSendableArray<int32_t,6>>" 
    (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) $ A.Array [dimension 6] A.Int32)
  ,testBoth "GenType 1101" "Channel" "csp::One2OneChannel<tockSendableArray<int32_t,6*7*8>>" 
    (tcall genType $ A.Chan A.DirUnknown (A.ChanAttributes False False) $ A.Array [dimension 6,dimension 7,dimension 8] A.Int32)


  -- List types:
  ,testBothS "GenType 2000" "GQueue*" "tockList<int16_t>" (tcall genType $ A.List A.Int16) markRainTest
  ,testBothS "GenType 2001" "GQueue*" "tockList<tockList<int16_t>>" (tcall genType $ A.List $ A.List A.Int16) markRainTest
  ,testBothS "GenType 2010" "GQueue**" "tockList<int16_t>" (tcall genType $ A.Mobile $ A.List A.Int16) markRainTest
  ,testBothS "GenType 2011" "GQueue**" "tockList<tockList<int16_t>>" (tcall genType $ A.Mobile $ A.List $ A.List A.Int16) markRainTest
  ,testBothS "GenType 2012" "GQueue**" "tockList<tockList<int16_t>>" (tcall genType $ A.Mobile $ A.List $ A.Mobile $ A.List A.Int16) markRainTest
 ]

testStop :: Test
testStop =
  testBoth "Stop" "occam_stop(\"foo:4:9\",1,\"bar\");" "throw StopException(\"foo:4:9\" \"bar\");" (tcall2 genStop (Meta (Just "foo") 4 9) "bar") 

testArraySizes :: Test
testArraySizes = TestList
 [
   testBothSame "genArrayLiteralElems 0" "$" $ unfolded (tcall genArrayLiteralElems [A.ArrayElemExpr undefined])
  ,testBothSame "genArrayLiteralElems 1" "$,$,$" $ unfolded (tcall genArrayLiteralElems [A.ArrayElemExpr undefined, A.ArrayElemExpr undefined, A.ArrayElemExpr undefined])
  ,testBothSame "genArrayLiteralElems 2" "$,$,$" $ unfolded (tcall genArrayLiteralElems [A.ArrayElemExpr undefined, A.ArrayElemArray [A.ArrayElemExpr undefined, A.ArrayElemExpr undefined]])
 ]
 where
  unfolded :: Override
  unfolded = local (\ops -> ops {genUnfoldedExpression = override1 dollar})

testActuals :: Test
testActuals = TestList
 [
  -- C adds a prefix comma (to follow Process* me) but C++ does not:
  testBoth "genActuals 0" ",@,@" "@,@" $ overActual (tcall genActuals [undefined, undefined] [undefined, undefined])
  ,testBothSame "genActuals 1" "" $ (tcall genActuals [] [])
  
  --For expressions, genExpression should be called:
  ,testBothSame "genActual 0" "$" $ over (tcall genActual valFormal $ A.ActualExpression (A.True undefined))
  ,testBothSame "genActual 1" "$" $ over (tcall genActual valFormal $ A.ActualExpression (A.Literal undefined undefined undefined))

  --The abbreviation mode used when generating an actual should come from the
  --corresponding formal, not from the variable:
  ,testBothSameS "genActual 10" "@" (over (tcall genActual valFormal $ A.ActualVariable (A.Variable undefined foo)))
    (defineVariable "foo" A.Int)
  ,testBothSameS "genActual 11" "&@" (over (tcall genActual refFormal $ A.ActualVariable (A.Variable undefined foo)))
    (defineVariable "foo" A.Int)
  ,testBothSameS "genActual 12" "@" (over (tcall genActual valFormal $ A.ActualVariable (A.Variable undefined foo)))
    (do defineVariable "bar" A.Int
        defineIs "foo" A.Int (variable "bar"))
  ,testBothSameS "genActual 13" "&@" (over (tcall genActual refFormal $ A.ActualVariable (A.Variable undefined foo)))
    (do defineVariable "bar" A.Int
        defineIs "foo" A.Int (variable "bar"))
 ]
 where
   valFormal :: A.Formal
   valFormal = A.Formal A.ValAbbrev undefined undefined
   refFormal :: A.Formal
   refFormal = A.Formal A.Abbrev undefined undefined
   overActual :: Override
   overActual = local (\ops -> ops {genActual = override2 at})
   over :: Override
   over = local (\ops -> ops {genVariable = override1 at, genExpression = override1 dollar})

-- TODO test the other two array checking methods   
testArraySubscript :: Test
testArraySubscript = TestList
 [
  testBothSameS "genArraySubscript 0" "[5*foo_sizes[1]*foo_sizes[2]]"
    (tcall3 genArraySubscript A.NoCheck (A.Variable emptyMeta foo) [lit 5]) stateTrans
  ,testBothSameS "genArraySubscript 1" "[5*foo_sizes[1]*foo_sizes[2]+6*foo_sizes[2]]"
    (tcall3 genArraySubscript A.NoCheck (A.Variable emptyMeta foo) [lit 5, lit 6]) stateTrans
  ,testBothSameS "genArraySubscript 2" "[5*foo_sizes[1]*foo_sizes[2]+6*foo_sizes[2]+7]"
    (tcall3 genArraySubscript A.NoCheck (A.Variable emptyMeta foo) [lit 5, lit 6, lit 7]) stateTrans
  
  ,testBothSameS "genArraySubscript 3" ("[occam_check_index(5,foo_sizes[0]," ++ m ++ ")*foo_sizes[1]*foo_sizes[2]]")
    (tcall3 genArraySubscript A.CheckBoth (A.Variable emptyMeta foo) [lit 5]) stateTrans
  ,testBothSameS "genArraySubscript 4"
    ("[occam_check_index(5,foo_sizes[0]," ++ m ++ ")*foo_sizes[1]*foo_sizes[2]+occam_check_index(6,foo_sizes[1]," ++ m ++ ")*foo_sizes[2]]")
    (tcall3 genArraySubscript A.CheckBoth (A.Variable emptyMeta foo) [lit 5, lit 6]) stateTrans
  ,testBothSameS "genArraySubscript 5"
    ("[occam_check_index(5,foo_sizes[0]," ++ m ++ ")*foo_sizes[1]*foo_sizes[2]+occam_check_index(6,foo_sizes[1]," ++ m ++ ")*foo_sizes[2]+occam_check_index(7,foo_sizes[2]," ++ m ++ ")]")
    (tcall3 genArraySubscript A.CheckBoth (A.Variable emptyMeta foo) [lit 5, lit 6, lit 7]) stateTrans
    
 ]
 where
   stateTrans :: CSM m => m ()
   stateTrans = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [dimension 7,dimension 8,dimension 8] A.Int)
   m = "\"" ++ show emptyMeta ++ "\""
   
   lit :: Int -> (Meta, CGen ())
   lit n = (emptyMeta, tell [show n])

testArraySlice :: Test
testArraySlice = TestList
 [
  -- Slice from a one-dimensional array:
  testSlice 0 ("(&arr[" ++ checkSlice "4" "5" "12" ++ "])") "arr" 4 5 [dimension 12]
    
  -- Slice from a two-dimensional array:
  ,testSlice 1 ("(&arr[" ++ checkSlice "4" "5" "12" ++ "*arr_sizes[1]])") "arr" 4 5 [dimension 12,dimension 12]
    
  -- Slice from a three-dimensional array:
  ,testSlice 2 ("(&arr[" ++ checkSlice "4" "5" "12" ++ "*arr_sizes[1]*arr_sizes[2]])") "arr" 4 5 [dimension 12,dimension 12,dimension 12]
  
  -- TODO test with unknown dimensions
 ]
 where
   testSlice :: Int -> String -> String -> Integer -> Integer -> [A.Dimension] -> Test
   testSlice index exp nm start count ds
     = testBothSameS ("genSlice " ++ show index) exp
      (tcall genVariable
        (A.SubscriptedVariable emptyMeta (A.SubscriptFromFor emptyMeta A.CheckBoth (intLiteral start) (intLiteral count)) (variable nm))
      )
      (defineName (simpleName nm) $ simpleDefDecl nm (A.Array ds A.Int))

   m = "\"" ++ show emptyMeta ++ "\""
   
   checkSlice s e sub = "occam_check_slice(" ++ s ++ "," ++ e ++ "," ++ sub ++ "," ++ m ++ ")"

-- TODO fix this test so that it tests fixed dimensions properly
testOverArray :: Test
testOverArray = TestList $ map testOverArray'
  [(cSize,cIndex,"", cgenOps)
  ,(cSize,cIndex,"", cppgenOps)
  ]
  where
    cSize n = "_sizes\\[" ++ show n ++ "\\]"

    cIndex x = "\\[" ++ concat (intersperse "\\+" $ map cIndex' x) ++ "\\]"
    cIndex' :: (String,[Int]) -> String
    cIndex' (s,ns) = s ++ concat (map (\n -> "\\*foo" ++ cSize n) ns)

    testOverArray' :: ((Int -> String),[(String,[Int])] -> String,String, GenOps) -> Test
    testOverArray' (sz,f',suff,ops) = TestCase $
      do testRS "testOverArray'" rx1Static (flip runReaderT ops $ tcall3 genOverArray emptyMeta (A.Variable emptyMeta foo) func) state1Static
         testRS "testOverArray'" rx1Dynamic (flip runReaderT ops $ tcall3 genOverArray emptyMeta (A.Variable emptyMeta foo) func) state1Dynamic
         testRS "testOverArray'" rx3Static (flip runReaderT ops $ tcall3 genOverArray emptyMeta (A.Variable emptyMeta foo) func) state3Static
         testRS "testOverArray'" rx3Dynamic (flip runReaderT ops $ tcall3 genOverArray emptyMeta (A.Variable emptyMeta foo) func) state3Dynamic
         return ()
      where
        func f = Just $ call genVariableUnchecked (f $ A.Variable emptyMeta foo) >> tell [";"]
        rx1Static = "^for\\(int ([[:alnum:]_]+)=0;\\1<7;\\1\\+\\+)\\{foo\\[\\1\\]" ++ suff ++ ";\\}$"
        rx1Dynamic = "^for\\(int ([[:alnum:]_]+)=0;\\1<foo" ++ sz 0 ++ ";\\1\\+\\+)\\{foo\\[\\1\\]" ++ suff ++ ";\\}$"
        rx3Static
           = "^for\\(int ([[:alnum:]_]+)=0;\\1<7;\\1\\+\\+)\\{" ++
              "for\\(int ([[:alnum:]_]+)=0;\\2<8;\\2\\+\\+)\\{" ++
              "for\\(int ([[:alnum:]_]+)=0;\\3<9;\\3\\+\\+)\\{" ++
              "foo" ++ (f' [("\\1",[1,2]),("\\2",[2]),("\\3",[])]) ++ suff ++ ";\\}\\}\\}$"
        rx3Dynamic
           = "^for\\(int ([[:alnum:]_]+)=0;\\1<foo" ++ sz 0 ++ ";\\1\\+\\+)\\{" ++
              "for\\(int ([[:alnum:]_]+)=0;\\2<8;\\2\\+\\+)\\{" ++
              "for\\(int ([[:alnum:]_]+)=0;\\3<foo" ++ sz 2 ++ ";\\3\\+\\+)\\{" ++
              "foo" ++ (f' [("\\1",[1,2]),("\\2",[2]),("\\3",[])]) ++ suff ++ ";\\}\\}\\}$"
        state1Static :: CSM m => m ()
        state1Static = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [dimension 7] A.Int)
        state1Dynamic :: CSM m => m ()
        state1Dynamic = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [A.UnknownDimension] A.Int)
        state3Static :: CSM m => m ()
        state3Static = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [dimension 7, dimension 8, dimension 9] A.Int)
        state3Dynamic :: CSM m => m ()
        state3Dynamic = defineName (simpleName "foo") $ simpleDefDecl "foo" (A.Array [A.UnknownDimension, dimension 8, A.UnknownDimension] A.Int)

testReplicator :: Test
testReplicator = TestList
 [
  testBothSame "testReplicator 0" "for(int foo=0;foo<10;foo++){" (tcall2 genReplicatorStart foo
    (A.For emptyMeta (intLiteral 0) (intLiteral 10)))
  ,testBothSameR "testReplicator 1" "for\\(int ([[:alnum:]_]+)=10,foo=1;\\1>0;\\1--,foo\\+\\+\\)\\{" (tcall2 genReplicatorStart
    foo (A.For emptyMeta (intLiteral 1) (intLiteral 10)))
 ]

testDeclaration :: Test
testDeclaration = TestList
 [
  --Simple: 
  testBothSame "genDeclaration 0" "int32_t foo;" (tcall3 genDeclaration A.Int32 foo False)
  
  --Channels and channel-ends:
  ,testBoth "genDeclaration 1" "Channel foo;" "csp::One2OneChannel<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int32) foo False)
  ,testBoth "genDeclaration 2" "Channel foo;" "csp::Any2OneChannel<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes True False) A.Int32) foo False)
  ,testBoth "genDeclaration 3" "Channel foo;" "csp::One2AnyChannel<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes False True) A.Int32) foo False)
  ,testBoth "genDeclaration 4" "Channel foo;" "csp::Any2AnyChannel<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirUnknown (A.ChanAttributes True True) A.Int32) foo False)
  ,testBoth "genDeclaration 5" "Channel* foo;" "csp::Chanin<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirInput (A.ChanAttributes False False) A.Int32) foo False)
  ,testBoth "genDeclaration 6" "Channel* foo;" "csp::Chanin<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirInput (A.ChanAttributes False True) A.Int32) foo False)
  ,testBoth "genDeclaration 7" "Channel* foo;" "csp::Chanout<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirOutput (A.ChanAttributes False False) A.Int32) foo False)
  ,testBoth "genDeclaration 8" "Channel* foo;" "csp::Chanout<int32_t> foo;" (tcall3 genDeclaration (A.Chan A.DirOutput (A.ChanAttributes True False) A.Int32) foo False)  
  
  --Arrays (of simple):
  ,testBothSame "genDeclaration 100" "int32_t foo[8];"
    (tcall3 genDeclaration (A.Array [dimension 8] A.Int32) foo False)
  ,testBothSame "genDeclaration 101" "int32_t foo[8*9];"
    (tcall3 genDeclaration (A.Array [dimension 8,dimension 9] A.Int32) foo False)
  ,testBothSame "genDeclaration 102" "int32_t foo[8*9*10];"
    (tcall3 genDeclaration (A.Array [dimension 8,dimension 9,dimension 10] A.Int32) foo False)

  --Arrays (of simple) inside records:
  ,testBothSame "genDeclaration 110" "int32_t foo[8];"
    (tcall3 genDeclaration (A.Array [dimension 8] A.Int32) foo True)
  ,testBothSame "genDeclaration 111" "int32_t foo[8*9];"
    (tcall3 genDeclaration (A.Array [dimension 8,dimension 9] A.Int32) foo True)
  ,testBothSame "genDeclaration 112" "int32_t foo[8*9*10];"
    (tcall3 genDeclaration (A.Array [dimension 8,dimension 9,dimension 10] A.Int32) foo True)
  
  --Arrays of channels and channel-ends:
  ,testBoth "genDeclaration 200" "Channel foo_storage[8];Channel* foo[8];"
    "csp::One2OneChannel<int32_t> foo_storage[8];csp::One2OneChannel<int32_t>* foo[8];"
    (tcall3 genDeclaration (A.Array [dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int32) foo False)

  ,testBoth "genDeclaration 201" "Channel foo_storage[8*9];Channel* foo[8*9];"
    "csp::One2OneChannel<int32_t> foo_storage[8*9];csp::One2OneChannel<int32_t>* foo[8*9];"
    (tcall3 genDeclaration (A.Array [dimension 8, dimension 9] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int32) foo False)
    
  ,testBoth "genDeclaration 202" "Channel* foo[8];"
    "csp::Chanin<int32_t> foo[8];"
    (tcall3 genDeclaration (A.Array [dimension 8] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int32) foo False)

  ,testBoth "genDeclaration 203" "Channel* foo[8*9];"
    "csp::Chanout<int32_t> foo[8*9];"
    (tcall3 genDeclaration (A.Array [dimension 8, dimension 9] $ A.Chan A.DirOutput (A.ChanAttributes False False) A.Int32) foo False)
    
    
  --Records of simple:
  ,testBothSameS "genDeclaration 300" "REC foo;" (tcall3 genDeclaration (A.Record $ simpleName "REC") foo False) (stateR A.Int32)
  
  --Records of arrays of int32_t (the sizes are set by declareInit):
  ,testBothSameS "genDeclaration 400" "REC foo;" (tcall3 genDeclaration (A.Record $ simpleName "REC") foo False) (stateR $ A.Array [dimension 8] A.Int32)

  --Timers:
  ,testBoth "genDeclaration 500" "Time foo;" "csp::Time foo;"
   (tcall3 genDeclaration (A.Timer A.OccamTimer) foo False)
  ,testBoth "genDeclaration 501" "Time foo[20];" "csp::Time foo[20];"
   (tcall3 genDeclaration (A.Array [dimension 20] (A.Timer A.OccamTimer)) foo False)
 ]
 where
   stateR t = defRecord "REC" "bar" t

testDeclareInitFree :: Test
testDeclareInitFree = TestLabel "testDeclareInitFree" $ TestList
 [
  -- Plain type:
  testAllSame 0 ("","") A.Int
  
  -- Channel types:
  ,testAll 1 ("ChanInit(wptr,(&foo));","") ("","") $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int
  ,testAllSame 2 ("","") $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int
  
  -- Plain arrays:
  ,testAllSame 3 ("","") $ A.Array [dimension 4] A.Int
  
  -- Channel arrays:
  ,testAll 4 ("tock_init_chan_array(foo_storage,foo,4);^ChanInit(wptr,foo[0]);^","") ("tockInitChanArray(foo_storage,foo,4);","") $ A.Array [dimension 4] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int
  ,testAllSame 6 ("","") $ A.Array [dimension 4] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int
  
  -- Plain records:
  ,testAllR 100 ("","") ("","") A.Int id
  -- Records containing an array:
  ,testAllR 101 ("","") ("","") (A.Array [dimension 4,dimension 5] A.Int) id
  -- Arrays of records containing an array:
  ,testAllRA 200 ("^^","") ("","") (A.Array [dimension 4,dimension 5] A.Int) id

  -- Mobile versions
  ,testAllSame 1003 ("","") $ A.Mobile $ A.Array [dimension 4] A.Int
  ,testAllSame 1004 ("","") $ A.Mobile $ A.Array [dimension 4] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int
  ,testAllR 1100 ("","") ("","") A.Int A.Mobile
  -- Records containing an array:
  ,testAllR 1101 ("","") ("","") (A.Array [dimension 4,dimension 5] A.Int) A.Mobile
  -- Arrays of records containing an array:
  ,testAllRA 1200 ("","") ("","") (A.Array [dimension 4,dimension 5] A.Int) A.Mobile
  

 ]
 where
   testAll :: Int -> (String,String) -> (String,String) -> A.Type -> Test
   testAll n eC eCPP t = testAll' n eC eCPP t (defineName (simpleName "foo") $ simpleDefDecl "foo" t)

   testAllR :: Int -> (String,String) -> (String,String) -> A.Type -> (A.Type -> A.Type) -> Test
   testAllR n eC eCPP t f = testAll' n eC eCPP (f $ A.Record $ simpleName "REC") ((defRecord "REC" "bar" t) >> (defineName (simpleName "foo") $ simpleDefDecl "foo" $ A.Record (simpleName "REC")))

   testAllRA :: Int -> (String,String) -> (String,String) -> A.Type -> (A.Type -> A.Type) -> Test
   testAllRA n eC eCPP t f = testAll' n eC eCPP (A.Array [dimension 5] $ f $ A.Record $ simpleName "REC") ((defRecord "REC" "bar" t) >> (defineName (simpleName "foo") $ simpleDefDecl "foo" $ A.Array [dimension 5] $ A.Record (simpleName "REC")))

   testAll' :: Int -> (String,String) -> (String,String) -> A.Type -> State CompState () -> Test
   testAll' n (iC,fC) (iCPP,fCPP) t state = TestList
    [
     testBothS ("testDeclareInitFree/a" ++ show n) ("@" ++ iC) ("@" ++ iCPP) (over (tcall introduceSpec $ A.Specification emptyMeta foo (A.Declaration emptyMeta t))) state
     ,testBothS ("testDeclareInitFree/b" ++ show n) iC iCPP (over $ ask >>= \ops -> (fromMaybe (return ())) (declareInit ops emptyMeta t (A.Variable emptyMeta foo))) state
     ,testBothS ("testDeclareInitFree/c" ++ show n) fC fCPP (over (tcall removeSpec $ A.Specification emptyMeta foo (A.Declaration emptyMeta t))) state
     ,testBothS ("testDeclareInitFree/d" ++ show n) fC fCPP (over $ ask >>= \ops -> (fromMaybe (return ())) (declareFree ops emptyMeta t (A.Variable emptyMeta foo))) state
    ]
     where
       overArray _ v f = case f (\v -> A.SubscriptedVariable emptyMeta (A.Subscript emptyMeta A.NoCheck $ intLiteral 0) v) of
         Just p -> caret >> p >> caret
         Nothing -> return ()
       over :: Override
       over = local $ \ops -> ops {genDeclaration = override3 at, genOverArray = overArray}

   testAllSame :: Int -> (String,String) -> A.Type -> Test
   testAllSame n e t = testAll n e e t

testRecord :: Test
testRecord = TestList
 [
  --Record types:
   testAllSame 400 ("typedef struct{#ATION_True}foo;","") foo False [(bar,A.Int)] 
  ,testAllSame 401 ("typedef struct{#ATION_True#ATION_True} occam_struct_packed foo;","") foo True [(bar,A.Int),(bar,A.Int)] 
  ,testAllSame 402 ("typedef struct{#ATION_True}foo;","") foo False [(bar,A.Array [dimension 6, dimension 7] A.Int)]
 ]
 where
    testAll :: Int -> (String,String) -> (String,String) -> A.Name -> Bool -> [(A.Name, A.Type)] -> Test
    testAll a b c0 c1 c2 d = testAllS a b c0 c1 c2 d (return ()) over
    
    testAllS :: Int -> (String,String) -> (String,String) -> A.Name ->  Bool -> [(A.Name, A.Type)] -> State CompState () -> (GenOps -> GenOps) -> Test
    testAllS n (eCI,eCR) (eCPPI,eCPPR) rn rb rts st overFunc
      = testBothS ("testRecord " ++ show n) eCI eCPPI (local overFunc (tcall genRecordTypeSpec rn rb rts)) st
    testAllSame n e s0 s1 s2 = testAll n e e s0 s1 s2
    over ops = ops {genDeclaration = override2 (tell . (\x -> ["#ATION_",show x]))
                   ,declareInit = (override3 (Just $ tell ["#INIT"])), declareFree = override3 (Just $ tell ["#FREE"])
                   ,genType = (\x -> tell ["$(",show x,")"])
                   ,genVariable = override1 at
                   }
 
testSpec :: Test
testSpec = TestList
 [
  --Declaration:
  testAllSame 0 ("#ATION_False#INIT","#FREE") $ A.Declaration emptyMeta A.Int
  ,testAllSame 1 ("#ATION_False#INIT","#FREE") $ A.Declaration emptyMeta (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testAllSame 2 ("#ATION_False#INIT","#FREE") $ A.Declaration emptyMeta (A.Array [dimension 3] A.Int)
  ,testAllSame 3 ("#ATION_False#INIT","#FREE") $ A.Declaration emptyMeta (A.Array [dimension 3] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)

  -- TODO test declarations with initialisers

  --Empty/failure cases:
  ,testAllSame 100 ("","") $ A.DataType undefined undefined
  ,testBothFail "testAllSame 200" (tcall introduceSpec $ A.Specification emptyMeta foo $ A.RetypesExpr emptyMeta A.Original A.Int (A.True emptyMeta))
  ,testBothFail "testAllSame 300" (tcall introduceSpec $ A.Specification emptyMeta foo $ A.Place emptyMeta (A.True emptyMeta))
  ,testAllSame 350 ("","") $ A.Protocol emptyMeta undefined

  --IsChannelArray:
  ,testAllSame 500 
    ("$(" ++ show chanInt ++ ")*foo[]={@,@};","")
    $ A.IsChannelArray emptyMeta (A.Array [dimension 2] $ chanInt) 
    [A.Variable undefined undefined,A.Variable undefined undefined]

  --Is:
  
  -- Plain types require you to take an address to get the pointer:
  ,testAllSameForTypes 600 (\t -> ("$(" ++ show t ++ ")*const foo=&bar;","")) (\t -> A.Is emptyMeta A.Abbrev t (variable "bar")) [A.Int,A.Time]
  ,testAllSameForTypes 610 (\t -> ("$(" ++ show t ++ ")*const foo=(&bar);","")) (\t -> A.Is emptyMeta A.Abbrev t (variable "bar")) [chanInt,A.Record foo]
  --Abbreviations of channel-ends in C++ should just copy the channel-end, rather than trying to take the address of the temporary returned by writer()/reader()
  --C abbreviations will be of type Channel*, so they can just copy the channel address.
  ,testAllForTypes 620 (\t -> ("$(" ++ show t ++ ") foo=bar;","")) (\t -> ("$(" ++ show t ++ ") foo=bar;",""))
    (\t -> A.Is emptyMeta A.Abbrev t (variable "bar")) [chanIntIn,chanIntOut]
  
  ,testAllSameForTypes 700 (\t -> ("const $(" ++ show t ++ ") foo=bar;","")) (\t -> A.Is emptyMeta A.ValAbbrev t (variable "bar")) [A.Int,A.Time]
  ,testAllSameForTypes 710 (\t -> ("const $(" ++ show t ++ ")*const foo=(&bar);","")) (\t -> A.Is emptyMeta A.ValAbbrev t (variable "bar")) [A.Record foo]
  -- I don't think ValAbbrev of channels/channel-ends makes much sense (occam doesn't support it, certainly) so they are not tested here.
  
  --TODO test Is more (involving subscripts, arrays and slices)

  --ProtocolCase:
  ,testAllSame 800 ("typedef enum{empty_protocol_foo}foo;","") $ A.ProtocolCase emptyMeta []
  ,testAllSame 801 ("typedef enum{bar_foo}foo;","") $ A.ProtocolCase emptyMeta [(bar,[])]
  ,testAllSame 802 ("typedef enum{bar_foo,wibble_foo}foo;","") $ A.ProtocolCase emptyMeta [(bar,[]),(simpleName "wibble",[])]
  
  --Retypes:
  -- Normal abbreviation:
  ,testAllSameS 900 ("int32_t*const foo=(int32_t*const)&y;@","") (A.Retypes emptyMeta A.Abbrev A.Int32 (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" A.Real32)) (\ops -> ops {genRetypeSizes = override5 at})
  -- Val abbreviation:
  ,testAllSameS 901 ("const int32_t foo=*(const int32_t*)&y;@","") (A.Retypes emptyMeta A.ValAbbrev A.Int32 (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" A.Real32)) (\ops -> ops {genRetypeSizes = override5 at})
  --Abbreviations of records as records:
  ,testAllSameS 910 ("bar*const foo=(bar*const)(&y);@","") (A.Retypes emptyMeta A.Abbrev (A.Record bar) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" (A.Record bar2))) (\ops -> ops {genRetypeSizes = override5 at})
  -- Val abbreviation of records as records:
  ,testAllSameS 911 ("const bar*const foo=(const bar*const)(&y);@","") (A.Retypes emptyMeta A.ValAbbrev (A.Record bar) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" (A.Record bar2))) (\ops -> ops {genRetypeSizes = override5 at})
     
  -- Channel retyping doesn't require size checking:
  ,testAllS 1000 ("Channel*const foo=(Channel*const)(&y);","") ("csp::One2OneChannel<tockSendableArrayOfBytes>*const foo=(csp::One2OneChannel<tockSendableArrayOfBytes>*const)(&y);","")
    (A.Retypes emptyMeta A.Abbrev (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Any) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Any))) id
      
  -- Plain-to-array retyping:
  -- single (unknown) dimension:
  ,testAllSameS 1100 ("uint8_t* foo=(uint8_t*)&y;@","")
    (A.Retypes emptyMeta A.Abbrev (A.Array [A.UnknownDimension] A.Byte) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" A.Int32)) (\ops -> ops {genRetypeSizes = override5 at})
  -- single (known) dimension:
  ,testAllSameS 1101 ("uint8_t* foo=(uint8_t*)&y;@","")
    (A.Retypes emptyMeta A.Abbrev (A.Array [dimension 4] A.Byte) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" A.Int32)) (\ops -> ops {genRetypeSizes = override5 at})
  -- single (unknown) dimension, VAL:
  ,testAllSameS 1102 ("const uint8_t* foo=(const uint8_t*)&y;@","")
    (A.Retypes emptyMeta A.ValAbbrev (A.Array [A.UnknownDimension] A.Byte) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" A.Int32)) (\ops -> ops {genRetypeSizes = override5 at})
  -- single (known) dimension, VAL:
  ,testAllSameS 1103 ("const uint8_t* foo=(const uint8_t*)&y;@","")
    (A.Retypes emptyMeta A.ValAbbrev (A.Array [dimension 4] A.Byte) (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" A.Int32)) (\ops -> ops {genRetypeSizes = override5 at})
  -- TODO test multiple dimensions plain-to-array (mainly for C++)
    
  -- Array-to-plain retyping:
  ,testAllSameS 1200 ("int32_t*const foo=(int32_t*const)y;@","")
    (A.Retypes emptyMeta A.Abbrev A.Int32 (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" (A.Array [A.UnknownDimension] A.Byte))) (\ops -> ops {genRetypeSizes = override5 at})
  ,testAllSameS 1201 ("const int32_t foo=*(const int32_t*)y;@","")
    (A.Retypes emptyMeta A.ValAbbrev A.Int32 (variable "y"))
    (defineName (simpleName "y") (simpleDefDecl "y" (A.Array [A.UnknownDimension] A.Byte))) (\ops -> ops {genRetypeSizes = override5 at})
  
  --TODO test array-to-array retyping  
  
  --TODO IsExpr
  --TODO Proc
 ]
  where
    testAllSameForTypes :: Int -> (A.Type -> (String, String)) -> (A.Type -> A.SpecType) -> [A.Type] -> Test
    testAllSameForTypes n te spec ts = testAllForTypes n te te spec ts

    testAllForTypes :: Int -> (A.Type -> (String, String)) -> (A.Type -> (String, String)) -> (A.Type -> A.SpecType) -> [A.Type] -> Test
    testAllForTypes n teC teCPP spec ts = TestList [testAllS (n+i) (teC t) (teCPP t) (spec t) (defineName (simpleName "bar") $ simpleDefDecl "bar" t) over' | (i,t) <- zip [0..] ts]
  
    chanInt = A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int
    chanIntIn = A.Chan A.DirInput (A.ChanAttributes False False) A.Int
    chanIntOut = A.Chan A.DirOutput (A.ChanAttributes False False) A.Int
  
    testAll :: Int -> (String,String) -> (String,String) -> A.SpecType -> Test
    testAll a b c d = testAllS a b c d (return ()) over
    
    testAllS :: Int -> (String,String) -> (String,String) -> A.SpecType -> State CompState () -> (GenOps -> GenOps) -> Test
    testAllS n (eCI,eCR) (eCPPI,eCPPR) spec st overFunc = TestList
     [
      testBothS ("testSpec " ++ show n) eCI eCPPI (local overFunc (tcall introduceSpec $ A.Specification emptyMeta foo spec)) st
      ,testBothS ("testSpec " ++ show n) eCR eCPPR (local overFunc (tcall removeSpec $ A.Specification emptyMeta foo spec)) st
     ]
    testAllSame n e s = testAll n e e s
    testAllSameS n e s st o = testAllS n e e s st o
    over' ops = ops {genDeclaration = override2 (tell . (\x -> ["#ATION_",show x]))
                   ,declareInit = (override3 (Just $ tell ["#INIT"])), declareFree = override3 (Just $ tell ["#FREE"])
                   ,genType = (\x -> tell ["$(",show x,")"])
                   }
    over ops = (over' ops) { genVariable = override1 at }
testRetypeSizes :: Test
testRetypeSizes = TestList
 [
  -- Channel retyping doesn't need size check:
  test 0 "" (A.Chan undefined undefined undefined) (A.Chan undefined undefined undefined)
  
  -- Plain types just need to check the return of occam_check_retype:
  ,test 1 "if(occam_check_retype(#S,#D,#M)!=1){@}"
    A.Int A.Int32
  ,test 2 "if(occam_check_retype(#S,#D,#M)!=1){@}"
    (A.Record foo) (A.Record bar)
    
  -- Array types where both sizes are fixed should act like the plain types:
  ,test 3 "if(occam_check_retype(#S,#D,#M)!=1){@}"
          (A.Array [dimension 2] A.Int) (A.Array [dimension 8] A.Byte)
  ,test 4 "if(occam_check_retype(#S,#D,#M)!=1){@}"
          (A.Array [dimension 2,dimension 3,dimension 4] A.Int) (A.Array [A.UnknownDimension] A.Byte)
    
  -- Array types with a free dimension should not check the return:
  ,test 100 "occam_check_retype(#S,#D,#M);"
    (A.Array [A.UnknownDimension] A.Int) (A.Array [dimension 8] A.Byte)
  ,test 101 "occam_check_retype(#S,#D,#M);"
    (A.Array [dimension 2,A.UnknownDimension,dimension 4] A.Int) (A.Array [A.UnknownDimension] A.Byte)
 ]
 where
   test :: Int -> String -> A.Type -> A.Type -> Test
   test n exp destT srcT = testBothSame ("testRetypeSizes " ++ show n) (repAll exp) 
     (over (tcall5 genRetypeSizes emptyMeta destT undefined srcT undefined))
     where
       repAll = (rep "#S" ("$(" ++ show srcT ++ " Right)")) .
                (rep "#D" ("$(" ++ show destT ++ " Left True)")) .
                (rep "#M" ("\"" ++ show emptyMeta ++ "\""))
  
   rep search replace str = subRegex (mkRegex search) str replace
 
   showBytesInParams _ t (Right _) = tell ["$(" ++ show t ++ " Right)"]
   showBytesInParams _ t v = tell ["$(" ++ show t ++ " " ++ show v ++ ")"]
   over :: Override
   over = local $ \ops -> ops {genBytesIn = showBytesInParams, genStop = override2 at}

defRecord :: String -> String -> A.Type -> State CompState ()
defRecord rec mem t = defineName (simpleName rec) $
  A.NameDef emptyMeta rec rec
    (A.RecordType emptyMeta False [(simpleName mem,t)])
    A.Original A.NameUser A.Unplaced

testGenVariable :: Test
testGenVariable = TestList
 [
  -- Various types, unsubscripted:
  testSameA 0 ("foo","(*foo)","foo") id A.Int
  ,testSameA 10 ("(&foo)","foo","foo") id (A.Record bar)
  ,testSameA2 20 ("(&foo)","foo") id (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testSameA2 30 ("foo","foo") id (A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
  
  -- Mobile versions of the above:
  ,testSameA2 40 ("foo","(*foo)") id (A.Mobile A.Int)
  ,testSameA2 45 ("(*foo)","(**foo)") deref (A.Mobile A.Int)
  ,testSameA2 50 ("foo","(*foo)") id (A.Mobile $ A.Record bar)
  ,testSameA2 55 ("foo","(*foo)") deref (A.Mobile $ A.Record bar)
  
  -- Arrays of the previous types, unsubscripted:
  ,testSameA 100 ("foo","foo","foo") id (A.Array [dimension 8] A.Int)
  ,testSameA 110 ("foo","foo","foo") id (A.Array [dimension 8] $ A.Record bar)
  ,testSameA2 120 ("foo","foo") id (A.Array [dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testSameA2 130 ("foo","foo") id (A.Array [dimension 8] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
  
  -- Mobile arrays of the previous types:
  ,testSameA2 140 ("foo","(*foo)") id (A.Mobile $ A.Array [dimension 8] A.Int)
  ,testSameA2 145 ("foo","(*foo)") deref (A.Mobile $ A.Array [dimension 8] A.Int)
  ,testSameA2 150 ("foo","(*foo)") id (A.Mobile $ A.Array [dimension 8] $ A.Record bar)  
  ,testSameA2 155 ("foo","(*foo)") deref (A.Mobile $ A.Array [dimension 8] $ A.Record bar)  
  
  -- Subscripted record:
  ,testSameA 200 ("(&foo)->x","foo->x","foo->x") fieldX (A.Record bar)
  ,testSameA2 210 ("foo->x","(*foo)->x") (fieldX . deref) (A.Mobile $ A.Record bar)
  
  ,testSameA 220 ("(&(&foo)->y)","(&foo->y)","(&foo->y)") fieldY (A.Record $ simpleName "barbar")
  ,testSameA 230 ("(&(&foo)->y)->x","(&foo->y)->x","(&foo->y)->x") (fieldX . fieldY) (A.Record $ simpleName "barbar")
  
  -- Fully subscripted array:
  ,testAC 300 ("foo@C4","foo@U4") (sub 4) (A.Array [dimension 8] A.Int)
  ,testAC 305 ("foo@C4,5,6","foo@U4,5,6") ((sub 6) . (sub 5) . (sub 4)) (A.Array [dimension 8,dimension 9,dimension 10] A.Int)
  ,testAC 310 ("(&foo@C4)","(&foo@U4)") (sub 4) (A.Array [dimension 8] $ A.Record bar)
  -- Original channel arrays are Channel*[], abbreviated channel arrays are Channel*[]:
  ,testAC2 320 ("foo@C4","foo@U4") ("foo@C4","foo@U4") (sub 4) (A.Array [dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testAC 330 ("foo@C4","foo@U4") (sub 4) (A.Array [dimension 8] $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int)
  
  -- Fully subscripted array, and record field reference:
  ,testAC 400 ("(&foo@C4)->x","(&foo@U4)->x") (fieldX . (sub 4)) (A.Array [dimension 8] $ A.Record bar)
  -- As above, but then with an index too:
  ,testAC 410 ("(&foo@C4)->x@C4","(&foo@U4)->x@U4") ((sub 4) . fieldX . (sub 4)) (A.Array [dimension 8] $ A.Record bar)
  
  --TODO come back to slices later
  
  -- Directed variables (incl. members of arrays, deref mobiles):
  ,testSameA2 500 ("$(&foo)$","$foo$") dir (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  -- Test for mobile channels (in future)
  --,testSameA2 510 ("$foo$","$(*foo)$") (dir . deref) (A.Mobile $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testAC2 520 ("$foo@C4$","$foo@U4$") ("$foo@C4$","$foo@U4$") (dir . (sub 4)) (A.Array [dimension 8] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
 ]
 where
   deref = A.DerefVariable emptyMeta
   dir = A.DirectedVariable emptyMeta A.DirInput
   fieldX = A.SubscriptedVariable emptyMeta (A.SubscriptField emptyMeta $ simpleName "x")
   fieldY = A.SubscriptedVariable emptyMeta (A.SubscriptField emptyMeta $ simpleName "y")
   sub n = A.SubscriptedVariable emptyMeta (A.Subscript emptyMeta A.CheckBoth $ intLiteral n)
 
   test :: Int -> (String,String) -> (String,String) -> (A.Variable -> A.Variable) -> A.AbbrevMode -> A.Type -> Test
   test n (eC,eUC) (eCPP,eUCPP) sub am t = TestList
    [
     testBothS ("testGenVariable/checked" ++ show n) eC eCPP (over (tcall genVariable $ sub $ A.Variable emptyMeta foo)) state
     ,testBothS ("testGenVariable/unchecked" ++ show n) eUC eUCPP (over (tcall genVariableUnchecked $ sub $ A.Variable emptyMeta foo)) state
    ]
     where
       state = do defineName (simpleName "foo") $
                    A.NameDef emptyMeta "foo" "foo"
                      (A.Declaration emptyMeta t) am A.NameUser A.Unplaced
                  defRecord "bar" "x" $ A.Array [dimension 7] A.Int
                  defRecord "barbar" "y" $ A.Record bar
       over :: Override
       over = local $ \ops -> ops {genArraySubscript = (\c _ subs -> at >> (tell [if c /= A.NoCheck then "C" else "U"]) >> (seqComma $ map snd subs))
                      ,genDirectedVariable = (\cg _ -> dollar >> cg >> dollar)}
   
   testA :: Int -> (String,String) -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testA n eC eCPP sub t = TestList [test n eC eCPP sub A.Original t, test (n+1) eC eCPP sub A.Abbrev t, test (n+2) eC eCPP sub A.ValAbbrev t]
   
   -- | Tests that the given (checked,unchecked) expected values occur in both C and C++
   testAC :: Int -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testAC n e sub t = testA n e e sub t

   -- | Tests that the given (checked,unchecked) expected values (for Original and Abbrev modes) occur in both C and C++
   testAC2 :: Int -> (String,String) -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testAC2 n e e' sub t = TestList [test n e e sub A.Original t, test (n+1) e' e' sub A.Abbrev t]
   
   testSame :: Int -> String -> (A.Variable -> A.Variable) -> A.AbbrevMode -> A.Type -> Test
   testSame n e sub am t = test n (e,e) (e,e) sub am t
   
   testSameA :: Int -> (String,String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testSameA n (eO,eA,eVA) sub t = TestList [testSame n eO sub A.Original t,testSame (n+1) eA sub A.Abbrev t,testSame (n+2) eVA sub A.ValAbbrev t]

   testSameA2 :: Int -> (String,String) -> (A.Variable -> A.Variable) -> A.Type -> Test
   testSameA2 n (eO,eA) sub t = TestList [testSame n eO sub A.Original t,testSame (n+1) eA sub A.Abbrev t]

testAssign :: Test
testAssign = TestList
 [
  testBothSameS "testAssign 0" "@=$;" (over (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e]))) (state A.Int)
  ,testBothSameS "testAssign 1" "@=$;" (over (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e]))) (state A.Time)
  ,testBothSameS "testAssign 2" "@=$;" (over (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e])))
    (state $ A.Chan A.DirInput (A.ChanAttributes False False) A.Int)

  -- Fail because genAssign only handles one destination and one source:
  ,testBothFail "testAssign 100" (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo,A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e]))
  ,testBothFail "testAssign 101" (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e,e]))
  ,testBothFail "testAssign 102" (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo,A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e, e]))
  
  -- Fail because assignment can't be done with these types (should have already been transformed away):
  ,testBothFailS "testAssign 200" (over (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e])))
    (state $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int)
  ,testBothFailS "testAssign 201" (over (tcall3 genAssign emptyMeta [A.Variable emptyMeta foo] (A.ExpressionList emptyMeta [e])))
    (state $ A.Record bar)
 ]
 where
   --The expression won't be examined so we can use what we like:
   e = A.True emptyMeta
   state t = defineName (simpleName "foo") $ simpleDefDecl "foo" t
   over :: Override
   over = local $ \ops -> ops {genVariable = override1 at, genExpression = override1 dollar}

testCase :: Test
testCase = TestList
 [
  testBothSame "testCase 0" "switch($){default:^}" (over (tcall3 genCase emptyMeta e (A.Several emptyMeta [])))
  ,testBothSame "testCase 1" "switch($){default:{@}break;}" (over (tcall3 genCase emptyMeta e (A.Only emptyMeta $ A.Else emptyMeta p)))
  ,testBothSame "testCase 2" "switch($){default:{#@}break;}" (over (tcall3 genCase emptyMeta e (spec $ A.Only emptyMeta $ A.Else emptyMeta p)))
  
  ,testBothSame "testCase 10" "switch($){case $:{@}break;default:^}" (over (tcall3 genCase emptyMeta e (A.Only emptyMeta $ A.Option emptyMeta [intLiteral 0] p)))

  ,testBothSame "testCase 20" "switch($){case $:case $:{#@}break;default:{@}break;case $:{@}break;}" (over (tcall3 genCase emptyMeta e $ A.Several emptyMeta
      [spec $ A.Only emptyMeta $ A.Option emptyMeta [e, e] p
      ,A.Only emptyMeta $ A.Else emptyMeta p
      ,A.Only emptyMeta $ A.Option emptyMeta [e] p]
    ))
 ]
  where
    --The expression and process won't be used so we can use what we like:
    e = A.True emptyMeta
    p = A.Skip emptyMeta
    spec :: Data a => A.Structured a -> A.Structured a
    spec = A.Spec emptyMeta undefined
    over :: Override
    over = local $ \ops -> ops {genExpression = override1 dollar, genProcess = override1 at, genStop = override2 caret, genSpec = override2 hash}

testIf :: Test
testIf = TestList
 [
  testBothR "testIf 0" "\\{\\^\\}" "\\{\\^\\}"
    (over (tcall2 genIf emptyMeta (A.Several emptyMeta [])))
  ,testBothR "testIf 1" "if\\(\\$\\)\\{@\\}else \\{\\^\\}" "if\\(\\$\\)\\{@\\}else \\{\\^\\}"
    (over (tcall2 genIf emptyMeta (A.Only emptyMeta $ A.Choice emptyMeta e p)))
  ,testBothR "testIf 2" "/\\*([[:alnum:]_]+)\\*/`if\\(\\$\\)\\{@goto \\1;\\}#\\^\\1:;" 
    "class ([[:alnum:]_]+)\\{\\};try\\{`if\\(\\$\\)\\{@throw \\1\\(\\);\\}#\\^\\}catch\\(\\1\\)\\{\\}"
    (over (tcall2 genIf emptyMeta (A.Spec emptyMeta undefined $ A.Only emptyMeta $ A.Choice emptyMeta e p)))
 ]
 where
   e :: A.Expression
   e = undefined
   p :: A.Process
   p = undefined
   over :: Override
   over = local $ \ops -> ops { genExpression = override1 dollar
                              , genProcess = override1 at
                              , genStop = override2 caret
                              , introduceSpec = override1 backq
                              , removeSpec = override1 hash}

testWhile :: Test
testWhile = testBothSame "testWhile 0" "while($){@}" (over (tcall2 genWhile undefined undefined))
  where
    over :: Override
    over = local $ \ops -> ops {genExpression = override1 dollar, genProcess = override1 at}

testInput :: Test
testInput = TestList
 [
  -- Test that genInput passes on the calls properly:
  testBothSame "testInput 0" "" (overInputItemCase (tcall2 genInput undefined $ A.InputSimple undefined []))
  ,testBothSame "testInput 1" "^" (overInputItemCase (tcall2 genInput undefined $ A.InputSimple undefined [undefined]))
  ,testBothSame "testInput 2" "^^^" (overInputItemCase (tcall2 genInput undefined $ A.InputSimple undefined [undefined, undefined, undefined]))
  
  -- Reading an integer (special case in the C backend):
  ,testInputItem 100 "ChanInInt(wptr,#,&x);" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int),&x));"
     (A.InVariable emptyMeta $ variable "x") A.Int
  -- Reading a other plain types:
  ,testInputItem 101 "ChanIn(wptr,#,&x,^(Int8));" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int8),&x));"
     (A.InVariable emptyMeta $ variable "x") A.Int8
  ,testInputItem 102 ("ChanIn(wptr,#,(&x),^(" ++ show (A.Record foo) ++ "));")
     ("tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(" ++ show (A.Record foo) ++ "),(&x)));")
     (A.InVariable emptyMeta $ variable "x") (A.Record foo)
  -- Reading into a fixed size array:
  ,testInputItem 103 "ChanIn(wptr,#,x,^(Array [Dimension 8] Int));"
      "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Array [Dimension 8] Int),x));"
       (A.InVariable emptyMeta $ variable "x") $ A.Array [dimension 8] A.Int
    
  -- Reading into subscripted variables:
  ,testInputItem 110 "ChanInInt(wptr,#,&xs$);" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int),&xs$));"
     (A.InVariable emptyMeta $ sub0 $ variable "xs") A.Int
  -- Reading a other plain types:
  ,testInputItem 111 "ChanIn(wptr,#,&xs$,^(Int8));" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int8),&xs$));"
     (A.InVariable emptyMeta $ sub0 $ variable "xs") A.Int8  
  ,testInputItem 112 ("ChanIn(wptr,#,(&xs$),^(" ++ show (A.Record foo) ++ "));")
    ("tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(" ++ show (A.Record foo) ++ "),(&xs$)));")
    (A.InVariable emptyMeta $ sub0 $ variable "xs") (A.Record foo)
  
  -- A counted array of Int:
  ,testInputItem 200 "ChanInInt(wptr,#,&x);ChanIn(wptr,#,xs,x*^(Int));"
    "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int),&x));tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(x*^(Int),xs));"
    (A.InCounted emptyMeta (variable "x") (variable "xs")) (A.Counted A.Int A.Int)
  -- A counted array, counted by Int8:
  ,testInputItem 201 "ChanIn(wptr,#,&x,^(Int8));ChanIn(wptr,#,xs,x*^(Int));"
    "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int8),&x));tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(x*^(Int),xs));"
    (A.InCounted emptyMeta (variable "x") (variable "xs")) (A.Counted A.Int8 A.Int)

  --  TODO reading in a counted/fixed-size array into an array of arrays (or will that have already been sliced?)

  -- inputs as part of protocols/any:
  ,testInputItemProt 300 "ChanInInt(wptr,#,&x);" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int),&x));"
    (A.InVariable emptyMeta $ variable "x") A.Int
  ,testInputItemProt 301 "ChanIn(wptr,#,&x,^(Int8));" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int8),&x));"
    (A.InVariable emptyMeta $ variable "x") A.Int8
  ,testInputItemProt 302 ("ChanIn(wptr,#,(&x),^(" ++ show (A.Record foo) ++ "));") ("tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(" ++ show (A.Record foo) ++ "),(&x)));")
    (A.InVariable emptyMeta $ variable "x") (A.Record foo)
  ,testInputItemProt 303 "ChanIn(wptr,#,x,^(Array [Dimension 8] Int));" "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Array [Dimension 8] Int),x));"
    (A.InVariable emptyMeta $ variable "x") $ A.Array [dimension 8] A.Int
  ,testInputItemProt 400 "ChanInInt(wptr,#,&x);ChanIn(wptr,#,xs,x*^(Int));"
    "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int),&x));tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(x*^(Int),xs));"
    (A.InCounted emptyMeta (variable "x") (variable "xs")) (A.Counted A.Int A.Int)
  ,testInputItemProt 401 "ChanIn(wptr,#,&x,^(Int8));ChanIn(wptr,#,xs,x*^(Int8));"
    "tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(^(Int8),&x));tockRecvArrayOfBytes(#,tockSendableArrayOfBytes(x*^(Int8),xs));"
    (A.InCounted emptyMeta (variable "x") (variable "xs")) (A.Counted A.Int8 A.Int8)

 ]
 where
   sub0 = A.SubscriptedVariable emptyMeta (A.Subscript emptyMeta A.NoCheck (intLiteral 0))
 
   testInputItem :: Int -> String -> String -> A.InputItem -> A.Type -> Test
   testInputItem n eC eCPP oi t = testInputItem' n eC eCPP oi t t
   -- Tests sending things over channels of protocol or ANY
   testInputItemProt :: Int -> String -> String -> A.InputItem -> A.Type -> Test
   testInputItemProt n eC eCPP oi t = TestList [testInputItem' n eC eCPP oi t (A.UserProtocol foo),testInputItem' n eC eCPP oi t A.Any]

   testInputItem' :: Int -> String -> String -> A.InputItem -> A.Type -> A.Type -> Test
   testInputItem' n eC eCPP ii t ct = TestList
     [
       testBothS ("testInput " ++ show n) (hashIs "(&c)" eC) (hashIs "(&c)->reader()" eCPP) (over (tcall2 genInputItem (A.Variable emptyMeta $ simpleName "c") ii)) (state A.DirUnknown)
       ,testBothS ("testInput [in] " ++ show n) (hashIs "c" eC) (hashIs "c" eCPP) (over (tcall2 genInputItem (A.Variable emptyMeta $ simpleName "c") ii)) (state A.DirInput)
     ]
     where
       hashIs x y = subRegex (mkRegex "#") y x
     
       state dir = do defineName (simpleName "c") $ simpleDefDecl "c" (A.Chan dir (A.ChanAttributes False False) ct)
                      case t of
                        A.Counted t t' -> do defineName (simpleName "x") $ simpleDefDecl "x" t
                                             defineName (simpleName "xs") $ simpleDefDecl "xs" (mkArray t')
                        _ -> do defineName (simpleName "x") $ simpleDefDecl "x" t
                                defineName (simpleName "xs") $ simpleDefDecl "xs" (mkArray t)
       mkArray (A.Array ds t) = A.Array (dimension 6:ds) t
       mkArray t = A.Array [dimension 6] t
 
--   chan = simpleName "c"
--   chanIn = simpleName "cIn"
--   state = do defineName chan $ simpleDefDecl "c" (A.Chan A.DirUnknown (A.ChanAttributes False False) $ A.UserProtocol foo)
--              defineName chanOut $ simpleDefDecl "cIn" (A.Chan A.DirInput (A.ChanAttributes False False) $ A.UserProtocol foo)

   overInputItemCase, over :: Override
   overInputItemCase = local $ \ops -> ops {genInputItem = override2 caret}
   over = local $ \ops -> ops {genBytesIn = (\_ t _ -> tell ["^(", showSimplerType t, ")"]) , genArraySubscript = override3 dollar}

   -- | Show a type, simplifying how Dimensions are show.
   showSimplerType :: A.Type -> String
   showSimplerType t = subRegex re (show t) "Dimension \\1"
     where re = mkRegex "Dimension [^\"]*\"([^\"]*)\"\\)\\)"

testOutput :: Test
testOutput = TestList
 [
  testBothSame "testOutput 0" "" (overOutputItem (tcall2 genOutput undefined []))
  ,testBothSame "testOutput 1" "^" (overOutputItem (tcall2 genOutput undefined [undefined]))
  ,testBothSame "testOutput 2" "^^^" (overOutputItem (tcall2 genOutput undefined [undefined,undefined,undefined]))
 
  ,testBothS "testOutput 100" "ChanOutInt(wptr,(&c),bar_foo);^" "tockSendInt((&c)->writer(),bar_foo);^" (overOutput (tcall3 genOutputCase (A.Variable emptyMeta chan) bar [])) state
  ,testBothS "testOutput 101" "ChanOutInt(wptr,cOut,bar_foo);^" "tockSendInt(cOut,bar_foo);^" (overOutput (tcall3 genOutputCase (A.Variable emptyMeta chanOut) bar [])) state
  
  --Integers are a special case in the C backend:
  ,testOutputItem 201 "ChanOutInt(wptr,#,x);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));"
    (A.OutExpression emptyMeta $ exprVariable "x") A.Int
  --A plain type on the channel of the right type:
  ,testOutputItem 202 "ChanOut(wptr,#,&x,^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));"
    (A.OutExpression emptyMeta $ exprVariable "x") A.Int64
  --A record type on the channel of the right type (because records are always referenced by pointer):
  ,testOutputItem 203 "ChanOut(wptr,#,(&x),^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes((&x)));"
    (A.OutExpression emptyMeta $ exprVariable "x") (A.Record foo)
  --A fixed size array on the channel of the right type:
  ,testOutputItem 204 "ChanOut(wptr,#,x,^);"
     "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(x));"
     (A.OutExpression emptyMeta $ exprVariable "x") (A.Array [dimension 6] A.Int)
  ,testOutputItem 205 "ChanOut(wptr,#,x,^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(x));"
    (A.OutExpression emptyMeta $ exprVariable "x") (A.Array [dimension 6, dimension 7, dimension 8] A.Int)

  --A counted array:
  ,testOutputItem 206 "ChanOutInt(wptr,#,x);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int A.Int)
  --A counted array of arrays:
  ,testOutputItem 207 "ChanOutInt(wptr,#,x);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int (A.Array [dimension 5] A.Int))
  ,testOutputItem 208 "ChanOutInt(wptr,#,x);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int (A.Array [dimension 4,dimension 5] A.Int))

  -- Test counted arrays that do not have Int as the count type:
  ,testOutputItem 209 "ChanOut(wptr,#,&x,^);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int8 A.Int8)
  
  
  --TODO add a pass that makes sure all outputs are variables.  Including count for counted items
  
  --Test sending things that are part of protocols (this will require different code in the C++ backend)
  ,testOutputItemProt 301 "ChanOutInt(wptr,#,x);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));"
    (A.OutExpression emptyMeta $ exprVariable "x") A.Int
  ,testOutputItemProt 302 "ChanOut(wptr,#,&x,^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));"
    (A.OutExpression emptyMeta $ exprVariable "x") A.Int64
  ,testOutputItemProt 303 "ChanOut(wptr,#,(&x),^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes((&x)));"
    (A.OutExpression emptyMeta $ exprVariable "x") (A.Record foo)
  ,testOutputItemProt 304 "ChanOut(wptr,#,x,^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(x));"
    (A.OutExpression emptyMeta $ exprVariable "x") (A.Array [dimension 6] A.Int)
  ,testOutputItemProt 305 "ChanOut(wptr,#,x,^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(x));"
    (A.OutExpression emptyMeta $ exprVariable "x") (A.Array [dimension 6, dimension 7, dimension 8] A.Int)
  ,testOutputItemProt 306 "ChanOutInt(wptr,#,x);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int A.Int)
  ,testOutputItemProt 307 "ChanOutInt(wptr,#,x);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int (A.Array [dimension 5] A.Int))
  ,testOutputItemProt 308 "ChanOutInt(wptr,#,x);ChanOut(wptr,#,xs,x*^);"
    "tockSendArrayOfBytes(#,tockSendableArrayOfBytes(&x));tockSendArrayOfBytes(#,tockSendableArrayOfBytes(xs));"
    (A.OutCounted emptyMeta (exprVariable "x") (exprVariable "xs")) (A.Counted A.Int (A.Array [dimension 4,dimension 5] A.Int))
    
    
  --TODO add tests for sending on channels that are part of (normal, and abbreviated) channel arrays.
 ]
 where
   testOutputItem :: Int -> String -> String -> A.OutputItem -> A.Type -> Test
   testOutputItem n eC eCPP oi t = testOutputItem' n eC eCPP oi t t
   -- Tests sending things over channels of protocol or ANY
   testOutputItemProt :: Int -> String -> String -> A.OutputItem -> A.Type -> Test
   testOutputItemProt n eC eCPP oi t = TestList [testOutputItem' n eC eCPP oi t (A.UserProtocol foo),testOutputItem' n eC eCPP oi t A.Any]

   testOutputItem' :: Int -> String -> String -> A.OutputItem -> A.Type -> A.Type -> Test
   testOutputItem' n eC eCPP oi t ct = TestList
     [
       testBothS ("testOutput " ++ show n) (hashIs "(&c)" eC) (hashIs "(&c)->writer()" eCPP) (over (tcall2 genOutputItem (A.Variable emptyMeta $ simpleName "c") oi)) (state A.DirUnknown)
       ,testBothS ("testOutput [out] " ++ show n) (hashIs "c" eC) (hashIs "c" eCPP) (over (tcall2 genOutputItem (A.Variable emptyMeta $ simpleName "c") oi)) (state A.DirOutput)
     ]
     where
       hashIs x y = subRegex (mkRegex "#") y x
     
       state dir = do defineName (simpleName "c") $ simpleDefDecl "c" (A.Chan dir (A.ChanAttributes False False) ct)
                      case t of
                        A.Counted t t' -> do defineName (simpleName "x") $ simpleDefDecl "x" t
                                             defineName (simpleName "xs") $ simpleDefDecl "xs" (mkArray t')
                        _ -> defineName (simpleName "x") $ simpleDefDecl "x" t
       mkArray (A.Array ds t) = A.Array (dimension 6:ds) t
       mkArray t = A.Array [dimension 6] t
 
   chan = simpleName "c"
   chanOut = simpleName "cOut"
   state :: CSM m => m ()
   state = do defineName chan $ simpleDefDecl "c" (A.Chan A.DirUnknown (A.ChanAttributes False False) $ A.UserProtocol foo)
              defineName chanOut $ simpleDefDecl "cOut" (A.Chan A.DirOutput (A.ChanAttributes False False) $ A.UserProtocol foo)
   overOutput, overOutputItem, over :: Override
   overOutput = local $ \ops -> ops {genOutput = override2 caret}
   overOutputItem = local $ \ops -> ops {genOutputItem = override2 caret}
   over = local $ \ops -> ops {genBytesIn = override3 caret}

testBytesIn :: Test
testBytesIn = TestList
 [
  testBothSame "testBytesIn 0" "sizeof(int8_t)" (tcall3 genBytesIn undefined A.Int8 undefined)
  ,testBothSame "testBytesIn 1" "sizeof(foo)" (tcall3 genBytesIn undefined (A.Record foo) undefined)
  ,testBoth "testBytesIn 2" "sizeof(Channel)" "sizeof(csp::One2OneChannel<int32_t>)" (tcall3 genBytesIn undefined (A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int32) undefined)
  ,testBoth "testBytesIn 3" "sizeof(Channel*)" "sizeof(csp::Chanin<int64_t>)" (tcall3 genBytesIn undefined (A.Chan A.DirInput (A.ChanAttributes False False) A.Int64) undefined)
  
  --Array with a single known dimension:
  ,testBothSame "testBytesIn 100" "5*sizeof(int16_t)" (tcall3 genBytesIn undefined (A.Array [dimension 5] A.Int16) (Left False))
  --single unknown dimension, no variable, no free dimension allowed:
  ,testBothFail "testBytesIn 101a" (tcall3 genBytesIn undefined (A.Array [A.UnknownDimension] A.Int) (Left False))
  --single unknown dimension, no variable, free dimension allowed:
  ,testBothSame "testBytesIn 101b" "sizeof(int16_t)" (tcall3 genBytesIn undefined (A.Array [A.UnknownDimension] A.Int16) (Left True))
  --single unknown dimension, with variable:
  ,testBothSame "testBytesIn 102" "$(@0)*sizeof(int32_t)" (over (tcall3 genBytesIn undefined (A.Array [A.UnknownDimension] A.Int32) (Right undefined)))
  
  --Array with all known dimensions:
  ,testBothSame "testBytesIn 200" "7*6*5*sizeof(int16_t)" (tcall3 genBytesIn undefined (A.Array [dimension 5,dimension 6, dimension 7] A.Int16) (Left False))
  --single unknown dimension, no variable, no free dimension allowed:
  ,testBothFail "testBytesIn 201a" (tcall3 genBytesIn undefined (A.Array [dimension 5,dimension 6,A.UnknownDimension] A.Int) (Left False))
  --single unknown dimension, no variable, free dimension allowed:
  ,testBothSame "testBytesIn 201b" "6*5*sizeof(int64_t)" (tcall3 genBytesIn undefined (A.Array [dimension 5,dimension 6,A.UnknownDimension] A.Int64) (Left True))
  --single unknown dimension, with variable:
  ,testBothSame "testBytesIn 202" "$(@2)*6*5*sizeof(int8_t)" (over (tcall3 genBytesIn undefined (A.Array [dimension 5,dimension 6,A.UnknownDimension] A.Int8) (Right undefined)))
  
 ]
 where
   over :: Override
   over = local $ \ops -> ops {genVariable = override1 dollar, genSizeSuffix = (\n -> tell["(@",n,")"])}

testMobile :: Test
testMobile = TestList
 [
  testBoth "testMobile 0" "malloc(#(Int Left False))" "new Int" (local over (tcall3 genAllocMobile emptyMeta (A.Mobile A.Int) Nothing))
  ,TestCase $ assertGen "testMobile 1/C++" "new Int($)" $ (evalCGen (call genAllocMobile emptyMeta (A.Mobile A.Int) (Just undefined)) (over cppgenOps) emptyState)
  
  ,testBoth "testMobile 100" "if(@!=NULL){free(@);@=NULL;}" "if(@!=NULL){delete @;@=NULL;}"
    (local over (tcall2 genClearMobile emptyMeta undefined))
 ]
  where
    showBytesInParams _ t (Right _) = tell ["#(" ++ show t ++ " Right)"]
    showBytesInParams _ t v = tell ["#(" ++ show t ++ " " ++ show v ++ ")"]
    over ops = ops {genBytesIn = showBytesInParams, genType = (\t -> tell [show t]), genExpression = override1 dollar, genVariable = override1 at}

---Returns the list of tests:
tests :: Test
tests = TestLabel "GenerateCTest" $ TestList
 [
   testActuals
   ,testArraySizes
   ,testArraySlice
   ,testArraySubscript
   ,testAssign
   ,testBytesIn
   ,testCase
   ,testDeclaration
   ,testDeclareInitFree
   ,testGenType
   ,testGenVariable
   ,testIf
   ,testInput
   ,testMobile
   ,testOutput
   ,testOverArray
   ,testRecord
   ,testReplicator
   ,testRetypeSizes
   ,testSpec
   ,testStop
   ,testWhile
 ]
