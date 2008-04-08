{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

module TestUtils where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import qualified Data.Map as Map
import System.Random
import Test.HUnit hiding (State,Testable)
import Test.QuickCheck

import qualified AST as A
import CompState
import Errors
import Metadata (emptyMeta)
import Pass
import Pattern
import PrettyShow
import TagAST
import TestFramework
import TreeUtils
import Types
import Utils

--{{{  utilities for QuickCheck tests

data QuickCheckLevel = QC_Low | QC_Medium | QC_High | QC_Extensive
  deriving (Show, Eq, Ord)

type QuickCheckTest = QuickCheckLevel -> Test

type LabelledQuickCheckTest = (String, QuickCheckTest)

-- | Adjust the size of a QuickCheck test depending on the check level.
scaleQC :: Testable a => (Int,Int,Int,Int) -> a -> QuickCheckTest
scaleQC (low,med,high,ext) test level
  = case level of
      QC_Low       -> run low test
      QC_Medium    -> run med test
      QC_High      -> run high test
      QC_Extensive -> run ext test
  where
    run :: Testable a => Int -> a -> Test
    run n = testCheck $ defaultConfig { configMaxTest = n }

-- | Run a QuickCheck test as an HUnit test.
testCheck :: Testable a => Config -> a -> Test
testCheck config property =
    TestCase $ do rnd <- newStdGen
                  tests config (evaluate property) rnd 0 0 []
  where
    -- | The 'tests' function from QuickCheck, modified to throw assertion
    -- failures when something goes wrong. (This is taken from MissingH.)
    tests :: Config -> Gen Result -> StdGen -> Int -> Int -> [[String]] -> IO ()
    tests config gen rnd0 ntest nfail stamps
      | ntest == configMaxTest config = return ()
      | nfail == configMaxFail config
        = assertFailure $ "Arguments exhausted after " ++ show ntest ++ " tests"
      | otherwise
        = case ok result of
            Nothing ->
              tests config gen rnd1 ntest (nfail+1) stamps
            Just True ->
              tests config gen rnd1 (ntest+1) nfail (stamp result:stamps)
            Just False ->
              assertFailure $ "Falsifiable, after " ++ show ntest
                              ++ " tests:\n" ++ unlines (arguments result)
         where
          result      = generate (configSize config ntest) rnd2 gen
          (rnd1,rnd2) = split rnd0

--}}}
--{{{  building AST fragments and patterns

-- | Helper function to generate an array dimension.
dimension :: Int -> A.Dimension
dimension n = makeDimension emptyMeta n

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

-- | Creates a char (Byte) literal with the given char
charLiteral :: Char -> A.Expression
charLiteral c = A.Literal emptyMeta A.Byte $ A.ByteLiteral emptyMeta [c]

-- | Creates an integer literal 'A.Expression' with the given integer.
integerLiteral :: A.Type -> Integer -> A.Expression
integerLiteral t n = A.Literal emptyMeta t $ A.IntLiteral emptyMeta (show n)

-- | Creates an 'A.Int' literal with the given integer.
intLiteral :: Integer -> A.Expression
intLiteral n = integerLiteral A.Int n

-- | Creates an 'A.Byte' literal with the given integer.
byteLiteral :: Integer -> A.Expression
byteLiteral n = integerLiteral A.Byte n

-- | Create an 'A.Bool' literal.
boolLiteral :: Bool -> A.Expression
boolLiteral b = if b then A.True emptyMeta else A.False emptyMeta

-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- @'assertPatternMatch' ('intLiteralPattern' x) ('intLiteral' x)@ will always succeed.
-- All meta tags are ignored.
intLiteralPattern :: Integer -> Pattern
intLiteralPattern = (stopCaringPattern emptyMeta) . mkPattern . intLiteral


-- | Creates an integer literal 'A.Expression' with the given integer.
int64Literal :: Integer -> A.Expression
int64Literal = integerLiteral A.Int64

int32Literal :: Integer -> A.Expression
int32Literal = integerLiteral A.Int32

-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- @'assertPatternMatch' ('intLiteralPattern' x) ('intLiteral' x)@ will always succeed.
-- All meta tags are ignored.
int64LiteralPattern :: Integer -> Pattern
int64LiteralPattern = (stopCaringPattern emptyMeta) . mkPattern . int64Literal

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
makeSeq procList = A.Seq emptyMeta $ A.Several emptyMeta (map (A.Only emptyMeta) procList)

-- | Turns a list of 'A.Process' into a 'A.Par' with those processes in order (with type 'A.PlainPar'), with empty meta tags.
makePar :: [A.Process] -> A.Process
makePar procList = A.Par emptyMeta A.PlainPar $ A.Several emptyMeta (map (A.Only emptyMeta) procList)

-- | Wraps the given process in a replicated 'A.Par' of the form PAR i = 0 FOR 3.
makeRepPar :: A.Process -> A.Process
makeRepPar proc = A.Par emptyMeta A.PlainPar $ A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (intLiteral 3)) (A.Only emptyMeta proc)

-- | Creates an assignment to the given 'A.Variable' from the given 'A.Expression.'
makeAssign :: A.Variable -> A.Expression -> A.Process
makeAssign v e = A.Assign emptyMeta [v] $ A.ExpressionList emptyMeta [e]

-- | Creates a 'Pattern' to match a 'A.Process' instance.
-- @'assertPatternMatch' ('makeAssignPattern' (mkPattern x) (mkPattern y)) ('makeAssign' x y)@ will always succeed.
-- All meta tags are ignored
makeAssignPattern :: Pattern -> Pattern -> Pattern
makeAssignPattern v e = tag3 A.Assign DontCare [v] $ tag2 A.ExpressionList DontCare [e]
 
-- | Creates a literal string expression from the given 'String'.
makeLiteralStringRain :: String -> A.Expression
makeLiteralStringRain str = A.Literal emptyMeta (A.List A.Byte) (A.ListLiteral emptyMeta (map makeLiteralChar str))
  where
    makeLiteralChar :: Char -> A.Expression
    makeLiteralChar c = A.Literal emptyMeta A.Byte (A.ByteLiteral emptyMeta [c] {-(show (fromEnum c))-})
    
-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- @'assertPatternMatch' ('makeLiteralStringPattern' x) ('makeLiteralString' x)@ will always succeed.
-- All meta tags are ignored
makeLiteralStringRainPattern :: String -> Pattern
makeLiteralStringRainPattern = (stopCaringPattern emptyMeta) . mkPattern . makeLiteralStringRain

-- | Creates a 'Pattern' to match an 'A.Expression' instance.
-- All meta tags are ignored
makeLiteralCharPattern :: Char -> Pattern
makeLiteralCharPattern c = tag3 A.Literal DontCare A.Byte (tag2 A.ByteLiteral DontCare [c])

makeListLiteralPattern :: [Pattern] -> Pattern
makeListLiteralPattern items = mLiteral (A.List A.Any) (mListLiteral items)

data ExprHelper = 
  Dy ExprHelper A.DyadicOp ExprHelper
  | Mon A.MonadicOp ExprHelper
  | Cast A.Type ExprHelper
  | Var String
  | DirVar A.Direction String
  | Lit A.Expression
  | EHTrue
  | Range A.Type ExprHelper ExprHelper
  | Func String [ExprHelper]

buildExprPattern :: ExprHelper -> Pattern
buildExprPattern = (stopCaringPattern emptyMeta) . mkPattern . buildExpr

buildExpr :: ExprHelper -> A.Expression
buildExpr (Dy lhs op rhs) = A.Dyadic emptyMeta op (buildExpr lhs) (buildExpr rhs)
buildExpr (Mon op rhs) = A.Monadic emptyMeta op (buildExpr rhs)
buildExpr (Cast ty rhs) = A.Conversion emptyMeta A.DefaultConversion ty (buildExpr rhs)
buildExpr (Var n) = A.ExprVariable emptyMeta $ variable n
buildExpr (DirVar dir n) = A.ExprVariable emptyMeta $ (A.DirectedVariable emptyMeta dir $ variable n)
buildExpr (Lit e) = e
buildExpr EHTrue = A.True emptyMeta
buildExpr (Range t begin end) = A.ExprConstr emptyMeta $ A.RangeConstr emptyMeta t
  (buildExpr begin) (buildExpr end)
buildExpr (Func f es) = A.FunctionCall emptyMeta ((simpleName f) {A.nameType
  = A.FunctionName}) (map buildExpr es)

-- | A simple definition of a variable
simpleDef :: String -> A.SpecType -> A.NameDef
simpleDef n sp = A.NameDef {A.ndMeta = emptyMeta, A.ndName = n, A.ndOrigName = n, A.ndNameType = A.VariableName,
                            A.ndType = sp, A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}

-- | A simple definition of a declared variable
simpleDefDecl :: String -> A.Type -> A.NameDef
simpleDefDecl n t = simpleDef n (A.Declaration emptyMeta t)

-- | A pattern that will match simpleDef, with a different abbreviation mode
simpleDefPattern :: String -> A.AbbrevMode -> Pattern -> Pattern
simpleDefPattern n am sp = tag7 A.NameDef DontCare n n A.VariableName sp am A.Unplaced

--}}}
--{{{  defining things

-- | Define something in the initial state.
defineThing :: String -> A.NameType -> A.SpecType -> A.AbbrevMode
               -> State CompState ()
defineThing s nt st am = defineName (simpleName s) $
    A.NameDef {
      A.ndMeta = emptyMeta,
      A.ndName = s,
      A.ndOrigName = s,
      A.ndNameType = nt,
      A.ndType = st,
      A.ndAbbrevMode = am,
      A.ndPlacement = A.Unplaced
    }

-- | Define a @VAL IS@ constant.
defineConst :: String -> A.Type -> A.Expression -> State CompState ()
defineConst s t e
    = defineThing s A.VariableName (A.IsExpr emptyMeta A.ValAbbrev t e)
                  A.ValAbbrev

-- | Define an @IS@ abbreviation.
defineIs :: String -> A.Type -> A.Variable -> State CompState ()
defineIs s t v
    = defineThing s A.VariableName (A.Is emptyMeta A.Abbrev t v) A.Abbrev

-- | Define a variable.
defineVariable :: String -> A.Type -> State CompState ()
defineVariable s t
    = defineThing s A.VariableName (A.Declaration emptyMeta t) A.Original

-- | Define a channel.
defineChannel :: String -> A.Type -> State CompState ()
defineChannel s t
    = defineThing s A.ChannelName (A.Declaration emptyMeta t) A.Original

-- | Define a timer.
defineTimer :: String -> A.Type -> State CompState ()
defineTimer s t
    = defineThing s A.TimerName (A.Declaration emptyMeta t) A.Original

-- | Define a user data type.
defineUserDataType :: String -> A.Type -> State CompState ()
defineUserDataType s t
    = defineThing s A.DataTypeName (A.DataType emptyMeta t) A.Original

-- | Define a record type.
-- (The fields are unscoped names, and thus don't need defining.)
defineRecordType :: String -> [(String, A.Type)] -> State CompState ()
defineRecordType s fs
    = defineThing s A.RecordName st A.Original
  where
    st = A.RecordType emptyMeta False [(simpleName s, t) | (s, t) <- fs]

-- | Define a function.
defineFunction :: String -> [A.Type] -> [(String, A.Type)]
                  -> State CompState ()
defineFunction s rs as
    = defineThing s A.FunctionName st A.Original
  where
    st = A.Function emptyMeta A.PlainSpec rs fs (Right $ A.Skip emptyMeta)
    fs = [A.Formal A.ValAbbrev t (simpleName s) | (s, t) <- as]

-- | Define a proc.
defineProc :: String -> [(String, A.AbbrevMode, A.Type)] -> State CompState ()
defineProc s as
    = defineThing s A.ProcName st A.Original
  where
    st = A.Proc emptyMeta A.PlainSpec fs $ A.Skip emptyMeta
    fs = [A.Formal am t (simpleName s) | (s, am, t) <- as]

-- | Define a protocol.
defineProtocol :: String -> [A.Type] -> State CompState ()
defineProtocol s ts
    = defineThing s A.ProtocolName (A.Protocol emptyMeta ts) A.Original

-- | Define a variant protocol.
defineProtocolCase :: String -> [(A.Name, [A.Type])] -> State CompState ()
defineProtocolCase s ntss
    = defineThing s A.ProtocolName (A.ProtocolCase emptyMeta ntss) A.Original

--}}}
--{{{  custom assertions

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

checkTempVarTypes :: String -> [(String, A.Type)] -> (Items, CompState) -> Assertion
checkTempVarTypes testName vars is = mapM_ (checkTempVarType testName is) vars
  where
    checkTempVarType :: String -> (Items, CompState) -> (String, A.Type) -> Assertion
    checkTempVarType testName (items, state) (key, t)
      = do (A.Name _ _ nm) <- castOrFail testName key items
           case Map.lookup nm (csNames state) of
             Nothing -> assertFailure (testName ++ ": item with key \"" ++ key ++ "\" was not recorded in the state")
             Just nd -> evalStateT (
                          do mtSpec <- typeOfSpec (A.ndType nd)
                             case mtSpec of
                               Just tSpec -> liftIO $ assertEqual (testName ++ ": type not as expected for key \"" ++ key ++ "\"") t tSpec
                               Nothing -> liftIO $ assertFailure (testName ++ ": spec does not have identifiable type for key \"" ++ key ++ "\": " ++ show (A.ndType nd))
                          ) state

assertEither :: (Eq a, Show a) => String -> a -> Either String a -> Assertion
assertEither testName exp = assertEqual testName (Right exp)
   
assertEitherFail :: String -> Either String a -> Assertion
assertEitherFail testName result
     = case result of
         Left _ -> return ()
         Right _ -> assertFailure $ testName ++ "; test expected to fail but passed"

--}}}
--{{{  canned tests

-- | Tests a given AST pass.  This function is primarily intended for internal use by this module.
-- It takes an expected value, a transformed value (wrapped in the 'PassM' monad), an initial state-changing function, and returns the subsequent
-- state, with either an assertion (if the pass failed) or the 'Items' (if the pass succeeded)
testPassGetItems :: 
  (Data a, Data b, TestMonad m r) =>
  String                                     -- ^ The message\/test name to prefix on failure.
  -> a                                       -- ^ The expected outcome of the pass.  Will be used as a 'Pattern', to find the named items in the result of the pass.
  -> PassM b                                 -- ^ The actual pass.
  -> (State CompState ())                    -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> m (CompState, Either (m ()) Items)        -- ^ Returns the state, along with either an 'Assertion' (if the pass fails) or the 'Items' (if the pass succeeds).
testPassGetItems testName expected actualPass startStateTrans = 
       --passResult :: Either String b
    do passResult <- runPass actualPass startState
       case passResult of
         (st, Left (_, err)) -> return (st, Left $ testFailure (prefixErr $ "pass actually failed: " ++ err)) 
         (st, Right resultItem) -> return (st, transformEither (mapM_ (testFailure . prefixErr)) (id) $ getMatchedItems expected resultItem)
       where
         startState :: CompState
         startState = execState startStateTrans emptyState

         prefixErr :: String -> String
         prefixErr err = testName ++ ": " ++ err


-- | Runs a given AST pass and returns the subsequent state, along with either an error or the result.  This function is primarily intended for internal use by this module.
runPass :: TestMonad m r =>
  PassM b                            -- ^ The actual pass.
  -> CompState                       -- ^ The state to use to run the pass.
  -> m (CompState, Either ErrorReport b) -- ^ The resultant state, and either an error or the successful outcome of the pass.
runPass actualPass startState = liftM (\(x,y,_) -> (y,x)) $
  runIO (runPassM startState actualPass)

-- | A test that runs a given AST pass and checks that it succeeds.
testPass ::
  (Data a, Data b, TestMonad m r) =>
  String                    -- ^ The test name.
  -> a                      -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                -- ^ The actual pass.
  -> (State CompState ())   -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> m ()
--If Items are returned by testPassGetItems we return () [i.e. give an empty assertion], otherwise give back the assertion:
testPass w x y z = join $ liftM (either (id) (\x -> return ())) $ (liftM snd) $ (testPassGetItems w x y z)

-- | A test that runs a given AST pass and checks that it succeeds, and performs an additional check on the result
testPassWithCheck ::
  (Data a, Data b, TestMonad m r) =>
  String                    -- ^ The test name.
  -> a                      -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                -- ^ The actual pass.
  -> (State CompState ())   -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> (b -> m ())
  -> m ()
testPassWithCheck testName expected actualPass startStateTrans checkFunc =
  do passResult <- runPass actualPass (execState startStateTrans emptyState)
     case snd passResult of
       Left (_,err) -> testFailure (testName ++ "; pass actually failed: " ++ err)
       Right result -> (testPatternMatch testName expected result) >> (checkFunc result)

-- | A test that runs a given AST pass, checks that it succeeds, and checks the resulting 'Items' with a given function.
testPassWithItemsCheck :: 
  (Data a, Data b, TestMonad m r) =>
  String                  -- ^ The test name.
  -> a                    -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b              -- ^ The actual pass.
  -> (State CompState ()) -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> (Items -> m ())      -- ^ A function to check the 'Items' once the pass succeeds.
  -> m ()
testPassWithItemsCheck testName expected actualPass startStateTrans checkFunc =
  ((liftM snd) (testPassGetItems testName expected actualPass startStateTrans))
  >>= (\res ->
    case res of 
      Left assert -> assert
      Right items -> checkFunc items
  )

-- | A test that runs a given AST pass, checks that it succeeds, and checks the resulting 'CompState' with a given function.
testPassWithStateCheck :: 
  (Data a, Data b, TestMonad m r) =>
  String                      -- ^ The test name.
  -> a                        -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                  -- ^ The actual pass.
  -> (State CompState ())     -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> (CompState -> m ())      -- ^ A function to check the 'CompState' once the pass succeeds.
  -> m ()
testPassWithStateCheck testName expected actualPass startStateTrans checkFunc =
  (testPassGetItems testName expected actualPass startStateTrans)
  >>= (\x ->
    case x of 
      (_,Left assert) -> assert
      (st,Right _) -> checkFunc st
  )

-- | A test that runs a given AST pass, checks that it succeeds, and checks the resulting 'CompState' and 'Items' with a given function.
testPassWithItemsStateCheck :: 
  (Data a, Data b, TestMonad m r) =>
  String                              -- ^ The test name.
  -> a                                -- ^ The expected value.  Can either be an actual AST, or a 'Pattern' to match an AST.
  -> PassM b                          -- ^ The actual pass.
  -> (State CompState ())             -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> ((Items,CompState) -> m ())      -- ^ A function to check the 'Items' and 'CompState' once the pass succeeds.
  -> m ()
testPassWithItemsStateCheck testName expected actualPass startStateTrans checkFunc =
  (testPassGetItems testName expected actualPass startStateTrans)
  >>= (\x ->
    case x of 
      (_,Left assert) -> assert
      (st,Right items) -> checkFunc (items,st)
  )
  
-- | A test that checks that a given AST pass fails.  If the pass fails, the test succeeds.  If the pass succeeds, the test fails.
testPassShouldFail :: 
  (Show b, Data b, TestMonad m r) => 
  String                  -- ^ The test name.
  -> PassM b              -- ^ The actual pass.
  -> (State CompState ()) -- ^ A function to transform a 'CompState'.  Will be used on the 'emptyState' to get the initial state for the pass.
  -> m ()
testPassShouldFail testName actualPass startStateTrans =
    do ret <- runPass actualPass (execState startStateTrans emptyState)
       case ret of
         (_,Left err) -> return ()
         (state, Right output) -> testFailure $ testName ++ " pass succeeded when expected to fail; output: " ++ pshow output

--}}}
--{{{  miscellaneous utilities

markRainTest :: State CompState ()
markRainTest = modify (\cs -> cs { csFrontend = FrontendRain })

castOrFail :: (Typeable b) => String -> String -> Items -> IO b
castOrFail testName key items = 
  case castADI (Map.lookup key items) of
    Just y -> return y
    Nothing -> do assertFailure (testName ++ ": could not find item")
                  -- Need this line so the types match:
                  fail ""

instance Die (StateT CompState IO) where
  dieReport (_,s) = liftIO $ do assertFailure s 
                                fail s

--}}}
