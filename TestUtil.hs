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

{-|

This TestUtil module contains useful helper functions for testing.  Examples of their use can be found in "RainPassTest" and "RainParseTest".
Unless otherwise stated, all functions use empty meta tags (see 'emptyMeta').

See also the 'TreeUtil.assertPatternMatch' function.


The Tock test framework is built on top of HUnit.  HUnit is a very simple test framework that is supplied by default with GHC:
<http://www.haskell.org/ghc/docs/latest/html/libraries/HUnit/Test-HUnit-Base.html>.  The only useful things to know are that:

> Assertion :: IO ()
> assertFailure :: String -> Assertion
> assertEqual :: (Eq a, Show a) => String -> a -> a -> Assertion

'assertFailure' is an assertion that fails with the given text message.  'assertEqual' checks if two things of the same type are equal.
If they are not equal, it shows them (using 'show') with the given message prefixed.

-}

module TestUtil where

import qualified AST as A
import Metadata (Meta,emptyMeta)
import Monad
import Test.HUnit hiding (State)
import Data.Generics
import Pattern
import TreeUtil
import Control.Monad.State
import Control.Monad.Error
import Pass
import CompState
import Utils
import qualified Data.Map as Map

-- | An abbreviation for using 'emptyMeta'.  TODO: This should really be removed (and all uses of it replaced with 'emptyMeta') for clarity.
m :: Meta
m = emptyMeta

-- | Creates a 'A.Name' object with the given 'String' as 'A.nameName', and 'A.nameType' as 'A.VariableName'.
simpleName :: String -> A.Name
simpleName s = A.Name { A.nameName = s , A.nameMeta = emptyMeta , A.nameType = A.VariableName }

-- | Creates a 'A.Name' object with the given 'String' as 'A.nameName', and 'A.nameType' as 'A.ProcName'.
procName :: String -> A.Name
procName s = A.Name { A.nameName = s , A.nameMeta = emptyMeta , A.nameType = A.ProcName }

-- | Creates a 'A.Name' object with the given 'String' as 'A.nameName', and 'A.nameType' as 'A.DataTypeName'.
typeName :: String -> A.Name
typeName s = A.Name { A.nameName = s , A.nameMeta = emptyMeta , A.nameType = A.DataTypeName }

-- | Creates a 'A.Name' object with the given 'String' as 'A.nameName', and 'A.nameType' as 'A.FunctionName'.
funcName :: String -> A.Name
funcName s = A.Name { A.nameName = s , A.nameMeta = emptyMeta , A.nameType = A.FunctionName }

-- | Creates a 'Pattern' to match a 'A.Name' instance.
-- @'assertPatternMatch' ('simpleNamePattern' x) ('simpleName' x)@ will always succeed.
-- All meta tags are ignored.
simpleNamePattern :: String -> Pattern
simpleNamePattern s = tag3 A.Name DontCare A.VariableName s

-- | Creates a 'Pattern' to match a 'A.Name' instance.
-- @'assertPatternMatch' ('procNamePattern' x) ('procName' x)@ will always succeed.
-- All meta tags are ignored.
procNamePattern :: String -> Pattern
procNamePattern s = tag3 A.Name DontCare A.ProcName s

-- | Creates a 'A.Variable' with the given 'String' as the name.
variable :: String -> A.Variable
variable e = A.Variable emptyMeta $ simpleName e

-- | Creates a 'Pattern' to match a 'A.Variable' instance.
-- @'assertPatternMatch' ('variablePattern' x) ('variable' x)@ will always succeed.
-- All meta tags are ignored.
variablePattern :: String -> Pattern
variablePattern e = tag2 A.Variable DontCare (simpleNamePattern e)

-- | Creates an 'A.Expression' that has the 'A.ExprVariable' constructor with the given 'String' as the variable name.
exprVariable :: String -> A.Expression
exprVariable e = A.ExprVariable emptyMeta $ variable e

-- | Creates an 'A.Expression' that has the 'A.ExprVariable' constructor with the given 'String' as the variable name in a 'A.DirectedVariable' with the given direction.
exprDirVariable :: A.Direction -> String -> A.Expression
exprDirVariable dir e = A.ExprVariable emptyMeta $ A.DirectedVariable emptyMeta dir $ variable e

-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- @'assertPatternMatch' ('exprVariablePattern' x) ('exprVariable' x)@ will always succeed.
-- All meta tags are ignored.
exprVariablePattern :: String -> Pattern
exprVariablePattern e = tag2 A.ExprVariable DontCare $ variablePattern e

-- | Creates an integer literal 'A.Expression' with the given integer.
intLiteral :: Integer -> A.Expression
intLiteral n = A.Literal emptyMeta A.Int $ A.IntLiteral emptyMeta (show n)

-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- @'assertPatternMatch' ('intLiteralPattern' x) ('intLiteral' x)@ will always succeed.
-- All meta tags are ignored.
intLiteralPattern :: Integer -> Pattern
intLiteralPattern = (stopCaringPattern emptyMeta) . mkPattern . intLiteral

-- | Creates a pair of variable lists, given a pair of variable-name lists as input.
makeNamesWR :: ([String],[String]) -> ([A.Variable],[A.Variable])
makeNamesWR (x,y) = (map variable x,map variable y)

-- | Creates a simple assignment ('A.Assign') 'A.Process', given two variable names.
makeSimpleAssign :: String -> String -> A.Process
makeSimpleAssign dest src = A.Assign emptyMeta [A.Variable emptyMeta $ simpleName dest] (A.ExpressionList emptyMeta [exprVariable src])

-- | Creates a 'Pattern' to match a 'A.Process' instance.
-- @'assertPatternMatch' ('makeSimpleAssignPattern' x y) ('makeSimpleAssign' x y)@ will always succeed.
-- All meta tags are ignored.
makeSimpleAssignPattern :: String -> String -> Pattern
makeSimpleAssignPattern lhs rhs = stopCaringPattern emptyMeta $ mkPattern $ makeSimpleAssign lhs rhs

-- | Turns a list of 'A.Process' into a 'A.Seq' with those processes in order, with empty meta tags.
makeSeq :: [A.Process] -> A.Process
makeSeq procList = A.Seq emptyMeta $ A.Several emptyMeta (map (\x -> A.OnlyP emptyMeta x) procList)

-- | Turns a list of 'A.Process' into a 'A.Par' with those processes in order (with type 'A.PlainPar'), with empty meta tags.
makePar :: [A.Process] -> A.Process
makePar procList = A.Par emptyMeta A.PlainPar $ A.Several emptyMeta (map (\x -> A.OnlyP emptyMeta x) procList)

-- | Wraps the given process in a replicated 'A.Par' of the form PAR i = 0 FOR 3.
makeRepPar :: A.Process -> A.Process
makeRepPar proc = A.Par emptyMeta A.PlainPar $ A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (intLiteral 3)) (A.OnlyP emptyMeta proc)

-- | Creates an assignment to the given 'A.Variable' from the given 'A.Expression.'
makeAssign :: A.Variable -> A.Expression -> A.Process
makeAssign v e = A.Assign emptyMeta [v] $ A.ExpressionList emptyMeta [e]

-- | Creates a 'Pattern' to match a 'A.Process' instance.
-- @'assertPatternMatch' ('makeAssignPattern' (mkPattern x) (mkPattern y)) ('makeAssign' x y)@ will always succeed.
-- All meta tags are ignored
makeAssignPattern :: Pattern -> Pattern -> Pattern
makeAssignPattern v e = tag3 A.Assign DontCare [v] $ tag2 A.ExpressionList DontCare [e]
 
-- | Creates a literal string expression from the given 'String'.
makeLiteralString :: String -> A.Expression
makeLiteralString str = A.Literal emptyMeta (A.Array [A.Dimension (length str)] A.Byte) (A.ArrayLiteral emptyMeta (map makeLiteralChar str))
  where
    makeLiteralChar :: Char -> A.ArrayElem
    makeLiteralChar c = A.ArrayElemExpr $ A.Literal emptyMeta A.Byte (A.ByteLiteral emptyMeta [c] {-(show (fromEnum c))-})
    
-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- @'assertPatternMatch' ('makeLiteralStringPattern' x) ('makeLiteralString' x)@ will always succeed.
-- All meta tags are ignored
makeLiteralStringPattern :: String -> Pattern
makeLiteralStringPattern = (stopCaringPattern emptyMeta) . mkPattern . makeLiteralString

-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- All meta tags are ignored
makeLiteralCharPattern :: Char -> Pattern
makeLiteralCharPattern c = tag3 A.Literal DontCare A.Byte (tag2 A.ByteLiteral DontCare [c])

-- | Asserts a comparison using a custom comparison function.
-- @'assertCompareCustom' msg (==) x y@ will function the same (except for slightly different messages on failure) as @'assertEqual' msg x y@.
assertCompareCustom :: 
  Show a => 
  String               -- ^ The message\/test name to prefix on failure.
  -> (a -> a -> Bool)  -- ^ The comparison function.  A return of True means the Assertion will succeed, False means the Assertion will fail.
  -> a                 -- ^ The expected\/yardstick value.
  -> a                 -- ^ The actual value from running the test.
  -> Assertion 
assertCompareCustom  preface cmp expected actual =
  unless (cmp actual expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ show expected ++ "\n*** got: " ++ show actual

-- | Asserts that the two given items are not equal.
-- Similar to assertEqual, but with the condition reversed.
assertNotEqual :: 
  (Show a,Eq a) => 
  String            -- ^ The message\/test name to prefix on failure.
  -> a              -- ^ The expected\/yardstick value that the actual value should not equal.
  -> a              -- ^ The actual value from running the test.
  -> Assertion
assertNotEqual msg = assertCompareCustom msg (/=)

-- | Asserts that two items in the Items set (by two given keys) are not the same, typically checking that an item has been transformed somehow.	  
-- This function is often used with 'testPassGetItems' or 'testPassWithCheck' or 'testPassWithItemsStateCheck'.
assertItemNotSame :: 
  String       -- ^ The message\/test name to prefix on failur
  -> Items     -- ^ The set of items after running the test.
  -> String    -- ^ The key of the untransformed original item 
  -> String    -- ^ The key of the new transformed item
  -> Assertion
assertItemNotSame msg items key0 key1 = assertNotEqual msg ((Map.lookup key0 items) :: Maybe AnyDataItem) ((Map.lookup key1 items) :: Maybe AnyDataItem)

-- | Tests a given AST pass.  This function is primarily intended for internal use by this module.
-- It takes an expected value, a transformed value (wrapped in the 'PassM' monad), an initial state-changing function, and returns the subsequent
-- state, with either an assertion (if the pass failed) or the 'Items' (if the pass succeeded)
testPassGetItems :: 
  (Data a, Data b) => 
  String                                     -- ^ The message\/test name to prefix on failure.
  -> a                                       -- ^ The expected outcome of the pass.  Will be used as a 'Pattern', to find the named items in the result of the pass.
  -> PassM b                                 -- ^ The actual pass.
  -> (State CompState ())                    -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> IO (CompState, Either Assertion Items)  -- ^ Returns the state, along with either an 'Assertion' (if the pass fails) or the 'Items' (if the pass succeeds).
testPassGetItems testName expected actualPass startStateTrans = 
       --passResult :: Either String b
    do passResult <- runPass actualPass startState
       case passResult of
         (st,Left err) -> return (st, Left $ assertFailure (testName ++ "; pass actually failed: " ++ err) )
         (st,Right resultItem) -> return (st, transformEither (sequence_ . map (assertFailure . ((++) testName))) (id) $ getMatchedItems expected resultItem )
       where
         startState :: CompState
         startState = execState startStateTrans emptyState

-- | Runs a given AST pass and returns the subsequent state, along with either an error or the result.  This function is primarily intended for internal use by this module.
runPass :: 
  PassM b                            -- ^ The actual pass.
  -> CompState                       -- ^ The state to use to run the pass.
  -> IO (CompState, Either String b) -- ^ The resultant state, and either an error or the successful outcome of the pass.
runPass actualPass startState = (liftM (\(x,y) -> (y,x))) (runStateT (runErrorT actualPass) startState)

-- | A test that runs a given AST pass and checks that it succeeds.
testPass :: 
  (Data a, Data b) => 
  String                    -- ^ The test name.
  -> a                      -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                -- ^ The actual pass.
  -> (State CompState ())   -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> Test
--If Items are returned by testPassGetItems we return () [i.e. give an empty assertion], otherwise give back the assertion:
testPass w x y z = TestCase $ join $ liftM (either (id) (\x -> return ())) $ (liftM snd) $ (testPassGetItems w x y z)

-- | A test that runs a given AST pass, checks that it succeeds, and checks the resulting 'Items' with a given function.
testPassWithCheck :: 
  (Data a, Data b) => 
  String                  -- ^ The test name.
  -> a                    -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b              -- ^ The actual pass.
  -> (State CompState ()) -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> (Items -> Assertion) -- ^ A function to check the 'Items' once the pass succeeds.
  -> Test
testPassWithCheck testName expected actualPass startStateTrans checkFunc = TestCase $
  ((liftM snd) (testPassGetItems testName expected actualPass startStateTrans))
  >>= (\res ->
    case res of 
      Left assert -> assert
      Right items -> checkFunc items
  )

-- | A test that runs a given AST pass, checks that it succeeds, and checks the resulting 'CompState' with a given function.
testPassWithStateCheck :: 
  (Data a, Data b) => 
  String                      -- ^ The test name.
  -> a                        -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                  -- ^ The actual pass.
  -> (State CompState ())     -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> (CompState -> Assertion) -- ^ A function to check the 'CompState' once the pass succeeds.
  -> Test
testPassWithStateCheck testName expected actualPass startStateTrans checkFunc = TestCase $
  (testPassGetItems testName expected actualPass startStateTrans)
  >>= (\x ->
    case x of 
      (_,Left assert) -> assert
      (st,Right _) -> checkFunc st
  )

-- | A test that runs a given AST pass, checks that it succeeds, and checks the resulting 'CompState' and 'Items' with a given function.
testPassWithItemsStateCheck :: 
  (Data a, Data b) => 
  String                              -- ^ The test name.
  -> a                                -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                          -- ^ The actual pass.
  -> (State CompState ())             -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> ((Items,CompState) -> Assertion) -- ^ A function to check the 'Items' and 'CompState' once the pass succeeds.
  -> Test
testPassWithItemsStateCheck testName expected actualPass startStateTrans checkFunc = TestCase $
  (testPassGetItems testName expected actualPass startStateTrans)
  >>= (\x ->
    case x of 
      (_,Left assert) -> assert
      (st,Right items) -> checkFunc (items,st)
  )
  
-- | A test that checks that a given AST pass fails.  If the pass fails, the test succeeds.  If the pass succeeds, the test fails.
testPassShouldFail :: 
  (Show b, Data b) => 
  String                  -- ^ The test name.
  -> PassM b              -- ^ The actual pass.
  -> (State CompState ()) -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> Test
testPassShouldFail testName actualPass startStateTrans = TestCase $
    do ret <- runPass actualPass (execState startStateTrans emptyState)
       case ret of
         (_,Left err) -> return ()
         _ -> assertFailure $ testName ++ " pass succeeded when expected to fail, data: " ++ (show ret)

-- | Asserts that a particular variable is defined in the given 'CompState'.
assertVarDef :: 
  String        -- ^ The message\/test name to prefix on failure.
  -> CompState  -- ^ The 'CompState' in which to check for the variable being defined
  -> String     -- ^ The name of the variable to check for.
  -> Pattern    -- ^ The expected value of the definition.  Expected to be a 'Pattern' that will match a 'A.NameDef'.
  -> Assertion
assertVarDef prefix state varName varDef 
  = case (Map.lookup varName (csNames state)) of
      Nothing -> assertFailure $ prefix ++ " variable was not recorded: " ++ varName
      Just actVarDef -> assertPatternMatch (prefix ++ " variable definition not as expected for " ++ varName) varDef actVarDef
