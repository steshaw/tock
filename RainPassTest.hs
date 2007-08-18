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

module RainPassTest (tests) where

import Test.HUnit hiding (State)
import Control.Monad.State as CSM
import qualified Data.Map as Map
import qualified AST as A
import TestUtil
import TreeUtil
import RainPasses
import CompState
import Control.Monad.Error (runErrorT)
import Control.Monad.Identity
import Types
import Pass
import Data.Generics
import Utils

-- | Helper function that checks two items in the Items set (by two given keys) are not the same
assertItemNotSame :: String -> Items -> String -> String -> Assertion
assertItemNotSame msg items key0 key1 = assertNotEqual msg ((Map.lookup key0 items) :: Maybe AnyDataItem) ((Map.lookup key1 items) :: Maybe AnyDataItem)

-- | Helper function that checks if a looked-up value is what was expected
assertItemNotEqual :: Data a => String -> a -> Maybe AnyDataItem -> Assertion
assertItemNotEqual msg _ Nothing = assertFailure $ msg ++ " item not matched!"
--Putting x into ADI wrapper and using the Eq instance for AnyDataItem is easier than taking y out and checking the data types match:
assertItemNotEqual msg exp (Just act) = assertNotEqual msg (ADI exp) act

testPassGetItems :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> IO (CompState, Either Assertion Items)
testPassGetItems testName expected actualPass startStateTrans = 
       --passResult :: Either String b
    do passResult <- runPass actualPass startState
       case passResult of
         (st,Left err) -> return (st, Left $ assertFailure (testName ++ "; pass actually failed: " ++ err) )
         (st,Right resultItem) -> return (st, transformEither (sequence_ . map (assertFailure . ((++) testName))) (id) $ getMatchedItems expected resultItem )
       where
         startState :: CompState
         startState = execState startStateTrans emptyState

runPass :: PassM b -> CompState -> IO (CompState, Either String b)
runPass actualPass startState = (liftM (\(x,y) -> (y,x))) (runStateT (runErrorT actualPass) startState)

testPass :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> Test
--If Items are returned by testPassGetItems we return () [i.e. give an empty assertion], otherwise give back the assertion:
testPass w x y z = TestCase $ join $ liftM (either (id) (\x -> return ())) $ (liftM snd) $ (testPassGetItems w x y z)

testPassWithCheck :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> (Items -> Assertion) -> Test
testPassWithCheck testName expected actualPass startStateTrans checkFunc = TestCase $
  ((liftM snd) (testPassGetItems testName expected actualPass startStateTrans))
  >>= (\res ->
    case res of 
      Left assert -> assert
      Right items -> checkFunc items
  )

testPassWithStateCheck :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> (CompState -> Assertion) -> Test
testPassWithStateCheck testName expected actualPass startStateTrans checkFunc = TestCase $
  (testPassGetItems testName expected actualPass startStateTrans)
  >>= (\x ->
    case x of 
      (_,Left assert) -> assert
      (st,Right _) -> checkFunc st
  )

testPassShouldFail :: (Show b, Data b) => String -> PassM b -> (State CompState ()) -> Test
testPassShouldFail testName actualPass startStateTrans = TestCase $
    do ret <- runPass actualPass (execState startStateTrans emptyState)
       case ret of
         (_,Left err) -> return ()
         _ -> assertFailure $ testName ++ " pass succeeded when expected to fail, data: " ++ (show ret)


simpleDef :: String -> A.SpecType -> A.NameDef
simpleDef n sp = A.NameDef {A.ndMeta = m, A.ndName = n, A.ndOrigName = n, A.ndNameType = A.VariableName,
                            A.ndType = sp, A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}

skipP :: A.Structured
skipP = A.OnlyP m (A.Skip m)


testEachPass0 :: Test
testEachPass0 = testPass "testEachPass0" exp (transformEach orig) startState'
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "c") $ simpleDef "c" (A.Declaration m A.Byte)
    
    orig = A.Seq m 
             (A.Rep m 
               (A.ForEach m (simpleName "c") (makeLiteralString "1")) 
               (A.OnlyP m (makeAssign (variable "c") (intLiteral 7)))              
             )
    exp = tag2 A.Seq DontCare
             (tag3 A.Spec DontCare
               (tag3 A.Specification DontCare listVarName
                 (tag4 A.IsExpr DontCare A.ValAbbrev (A.Array [A.Dimension 1] A.Byte) (makeLiteralString "1"))
               )
               (tag3 A.Rep DontCare
                 (tag4 A.For DontCare indexVar (intLiteral 0) (tag2 A.SizeVariable DontCare listVar))
                 (tag3 A.Spec DontCare 
                   (tag3 A.Specification DontCare (simpleName "c") 
                     (tag4 A.Is DontCare A.Abbrev A.Byte
                       (tag3 A.SubscriptedVariable DontCare 
                         (tag2 A.Subscript DontCare (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare indexVar)))
                         listVar
                       )
                     )
                   )
                   (A.OnlyP m (makeAssign (variable "c") (intLiteral 7)))
                 )
               )
             )
    indexVar = Named "indexVar" DontCare
    listVarName = Named "listVarName" DontCare
    listVar = tag2 A.Variable DontCare listVarName


testEachPass1 :: Test
testEachPass1 = testPass "testEachPass0" exp (transformEach orig) startState'
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "c") $ simpleDef "c" (A.Declaration m A.Byte)
                     defineName (simpleName "d") $ simpleDef "d" (A.Declaration m (A.Array [A.Dimension 10] A.Byte))

    orig = A.Par m A.PlainPar
             (A.Rep m
               (A.ForEach m (simpleName "c") (A.ExprVariable m (variable "d")))
               (A.OnlyP m (makeAssign (variable "c") (intLiteral 7)))
             )
    exp = tag3 A.Par DontCare A.PlainPar
             (tag3 A.Rep DontCare
               (tag4 A.For DontCare indexVar (intLiteral 0) (tag2 A.SizeVariable DontCare (variable "d")))
               (tag3 A.Spec DontCare
                 (tag3 A.Specification DontCare (simpleName "c")
                   (tag4 A.Is DontCare A.Abbrev A.Byte
                     (tag3 A.SubscriptedVariable DontCare
                       (tag2 A.Subscript DontCare (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare indexVar)))
                       (variable "d")
                     )
                   )
                 )
                 (A.OnlyP m (makeAssign (variable "c") (intLiteral 7)))
               )
             )
    indexVar = Named "indexVar" DontCare

-- | Test variable is made unique in a declaration:
testUnique0 :: Test
testUnique0 = testPassWithCheck "testUnique0" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) skipP
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte) skipP
    check items = assertItemNotEqual "testUnique0: Variable was not made unique" (simpleName "c") (Map.lookup "newc" items)

-- | Tests that two declarations of a variable with the same name are indeed made unique:
testUnique1 :: Test
testUnique1 = testPassWithCheck "testUnique1" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Several m [A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) skipP,
                        A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Int) skipP]
    exp = tag2 A.Several m [tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc0" DontCare) $ A.Declaration m $ A.Byte) skipP,
                            tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc1" DontCare) $ A.Declaration m $ A.Int) skipP]
    check items = do assertItemNotEqual "testUnique1: Variable was not made unique" (simpleName "c") (Map.lookup "newc0" items)
                     assertItemNotEqual "testUnique1: Variable was not made unique" (simpleName "c") (Map.lookup "newc1" items)
                     assertItemNotSame "testUnique1: Variables were not made unique" items "newc0" "newc1"

-- | Tests that the unique pass does resolve the variables that are in scope
testUnique2 :: Test
testUnique2 = testPassWithCheck "testUnique2" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) (A.OnlyP m $ makeSimpleAssign "c" "d")
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte) 
      (tag2 A.OnlyP m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "newc" DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "d")]))
    check items = assertItemNotEqual "testUnique2: Variable was not made unique" (simpleName "c") (Map.lookup "newc" items)

assertVarDef :: Data a => String -> CompState -> String -> a -> Assertion
assertVarDef prefix state varName varDef 
  = case (Map.lookup varName (csNames state)) of
      Nothing -> assertFailure $ prefix ++ " variable was not recorded: " ++ varName
      Just actVarDef -> assertPatternMatch (prefix ++ " variable definition not as expected for " ++ varName) varDef actVarDef


testRecordDeclNames0 :: Test
testRecordDeclNames0 = testPassWithStateCheck "testRecordDeclNames0" exp (recordDeclNameTypes orig) (return ()) check
  where
    orig = (A.Specification m (simpleName "c") $ A.Declaration m A.Byte)
    exp = orig
    check state = assertVarDef "testRecordDeclNames0" state "c" 
      (tag7 A.NameDef DontCare "c" "c" A.VariableName (A.Declaration m A.Byte) A.Original A.Unplaced)

-- | checks that c's type is recorded in: ***each (c : "hello") {}
testRecordInfNames0 :: Test
testRecordInfNames0 = testPassWithStateCheck "testRecordInfNames0" exp (recordInfNameTypes orig) (return ()) check
  where
    orig =  (A.Rep m (A.ForEach m (simpleName "c") (makeLiteralString "hello")) skipP)
    exp = orig
    check state = assertVarDef "testRecordInfNames0" state "c" 
      (tag7 A.NameDef DontCare "c" "c" A.VariableName (A.Declaration m A.Byte) A.Original A.Unplaced)
      
-- | checks that c's type is recorded in: ***each (c : str) {}, where str is known to be of type string
testRecordInfNames1 :: Test
testRecordInfNames1 = testPassWithStateCheck "testRecordInfNames1" exp (recordInfNameTypes orig) (startState') check
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "str") $ simpleDef "str" (A.Declaration m (A.Array [A.Dimension 10] A.Byte))
    orig =  (A.Rep m (A.ForEach m (simpleName "c") (exprVariable "str")) skipP)
    exp = orig
    check state = assertVarDef "testRecordInfNames1" state "c" 
      (tag7 A.NameDef DontCare "c" "c" A.VariableName (A.Declaration m A.Byte) A.Original A.Unplaced)      

-- | checks that c's and d's type are recorded in: ***each (c : multi) { seqeach (d : c) {} } where multi is known to be of type [string]
testRecordInfNames2 :: Test
testRecordInfNames2 = testPassWithStateCheck "testRecordInfNames2" exp (recordInfNameTypes orig) (startState') check
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "multi") $ simpleDef "multi" (A.Declaration m (A.Array [A.Dimension 10, A.Dimension 20] A.Byte))
    orig =  A.Rep m (A.ForEach m (simpleName "c") (exprVariable "multi")) $
      A.OnlyP m $ A.Seq m $ A.Rep m (A.ForEach m (simpleName "d") (exprVariable "c")) skipP
    exp = orig
    check state = do assertVarDef "testRecordInfNames2" state "c" 
                      (tag7 A.NameDef DontCare "c" "c" A.VariableName (A.Declaration m (A.Array [A.Dimension 20] A.Byte)) A.Original A.Unplaced)
                     assertVarDef "testRecordInfNames2" state "d" 
                      (tag7 A.NameDef DontCare "d" "d" A.VariableName (A.Declaration m A.Byte) A.Original A.Unplaced)                          

-- | checks that doing a foreach over a non-array type is barred:
testRecordInfNames3 :: Test
testRecordInfNames3 = testPassShouldFail "testRecordInfNames3" (recordInfNameTypes orig) (return ())
  where
    orig = A.Rep m (A.ForEach m (simpleName "c") (intLiteral 0)) skipP

--Returns the list of tests:
tests :: Test
tests = TestList
 [
   testEachPass0
   ,testEachPass1
   ,testUnique0
   ,testUnique1
   ,testUnique2
   ,testRecordDeclNames0
   ,testRecordInfNames0
   ,testRecordInfNames1
   ,testRecordInfNames2
   ,testRecordInfNames3
 ]


