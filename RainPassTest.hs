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

testPassGetItems :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> IO (Either Assertion Items)
testPassGetItems testName expected actualPass startStateTrans = 
       --passResult :: Either String b
    do passResult <- runPass actualPass    
       case passResult of
         Left err -> return $ Left $ assertFailure (testName ++ "; pass actually failed: " ++ err)
         Right resultItem -> return $ transformEither (sequence_ . map (assertFailure . ((++) testName))) (id) $ getMatchedItems expected resultItem
       where
         runPass :: PassM b -> IO (Either String b)
         runPass actualPass = (evalStateT (runErrorT actualPass) (execState startStateTrans emptyState))

testPass :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> Test
--If Items are returned by testPassGetItems we return () [i.e. give an empty assertion], otherwise give back the assertion:
testPass w x y z = TestCase $ join $ liftM (either (id) (\x -> return ())) $ (testPassGetItems w x y z)

testPassWithCheck :: (Data a, Data b) => String -> a -> PassM b -> (State CompState ()) -> (Items -> Assertion) -> Test
testPassWithCheck testName expected actualPass startStateTrans checkFunc = TestCase $
  (testPassGetItems testName expected actualPass startStateTrans) 
  >>= (\res ->
    case res of 
      Left assert -> assert
      Right items -> checkFunc items
  )

testEachPass0 :: Test
testEachPass0 = testPass "testEachPass0" exp (transformEach orig) startState'
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "c") A.NameDef {A.ndType = A.Declaration m A.Byte}
    
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
    startState' = do defineName (simpleName "c") A.NameDef {A.ndType = A.Declaration m A.Byte}
                     defineName (simpleName "d") A.NameDef {A.ndType = A.Declaration m (A.Array [A.Dimension 10] A.Byte)}

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
testUnique0 = testPassWithCheck "testUnique0" exp (uniquifyVars orig) (return ()) check
  where
    orig = A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte    
    exp = tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte
    check items = assertItemNotEqual "testUnique0: Variable was not made unique" (simpleName "c") (Map.lookup "newc" items)

-- | Tests that two declarations of a variable with the same name are indeed made unique:
testUnique1 :: Test
testUnique1 = testPassWithCheck "testUnique1" exp (uniquifyVars orig) (return ()) check
  where
    orig = A.Several m [A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) skipP,
                        A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Int) skipP]
    exp = tag2 A.Several m [tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc0" DontCare) $ A.Declaration m $ A.Byte) skipP,
                            tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc1" DontCare) $ A.Declaration m $ A.Int) skipP]
    skipP = A.OnlyP m (A.Skip m)
    check items = do assertItemNotEqual "testUnique1: Variable was not made unique" (simpleName "c") (Map.lookup "newc0" items)
                     assertItemNotEqual "testUnique1: Variable was not made unique" (simpleName "c") (Map.lookup "newc1" items)
                     assertItemNotSame "testUnique1: Variables were not made unique" items "newc0" "newc1"

-- | Tests that the unique pass does not change variables that are not in declarations
testUnique2 :: Test
testUnique2 = testPassWithCheck "testUnique2" exp (uniquifyVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) (A.OnlyP m $ makeSimpleAssign "c" "d")
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte) (A.OnlyP m $ makeSimpleAssign "c" "d")
    check items = assertItemNotEqual "testUnique2: Variable was not made unique" (simpleName "c") (Map.lookup "newc" items)



--Returns the list of tests:
tests :: Test
tests = TestList
 [
   testEachPass0
   ,testEachPass1
   ,testUnique0
   ,testUnique1
   ,testUnique2
 ]


