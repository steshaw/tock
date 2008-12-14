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

-- | This file has tests for various Rain passes.  The tests are quite nasty to look at.
-- They usually consist of a hand-constructed AST fragment that is the input to the test.
-- The expected output is either a resulting AST, or a check on the items matched in the pattern.
-- This stuff is all built on top of the Pattern system, which you can find more about in the
-- Pattern, TreeUtils and TestUtils module.  Briefly, it is an easy way to match an actual test
-- result against an expected pattern, that may have special features in it.  See the other module
-- documentation.
--
-- TODO document each test in this file.
module RainPassesTest (tests) where

import Control.Monad.State
import Control.Monad.Identity
import Data.Generics
import qualified Data.Map as Map
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Errors
import Metadata
import Pass
import Pattern
import RainPasses
import RainTypes
import TagAST
import TestUtils
import TreeUtils
import Types
import Utils

m :: Meta
m = emptyMeta

-- | A helper function that returns a simple A.Structured A.Process item (A.Only m $ A.Skip m).
skipP :: A.Structured A.Process
skipP = A.Only m (A.Skip m)

-- | A function that tries to cast a given value into the return type, and dies (using "dieInternal")
-- if the cast isn't valid.
castAssertADI :: (Typeable b) => Maybe AnyDataItem -> IO b
castAssertADI x = case (castADI x) of
  Just y -> return y
  Nothing -> dieInternal (Nothing, "Pattern successfully matched but did not find item afterwards")

makeRange :: Integer -> Integer -> A.Expression
makeRange b e = addExprsInt (intLiteral 1)
  (subExprsInt (intLiteral e) (intLiteral b))

testEachRangePass0 :: Test
testEachRangePass0 = TestCase $ testPass "testEachRangePass0" exp transformEachRange orig (return ())
  where
    orig = A.Par m A.PlainPar $ A.Spec m (A.Specification m (simpleName "x")
               $ A.Rep m (A.ForEach m (A.Literal m (A.List A.Int) (A.RangeLiteral m
                 (intLiteral 0) (intLiteral 9)))))
               (A.Only m (makeSimpleAssign "c" "x"))
    exp = A.Par m A.PlainPar $ A.Spec m (A.Specification m (simpleName "x")
               $ A.Rep m (A.For m (intLiteral 0) (makeRange 0 9) (intLiteral 1)))
               (A.Only m (makeSimpleAssign "c" "x"))
               
testEachRangePass1 :: Test
testEachRangePass1 = TestCase $ testPass "testEachRangePass1" exp transformEachRange orig (return ())
  where
    orig = A.Par m A.PlainPar $ A.Spec m (A.Specification m (simpleName "x")
               $ A.Rep m (A.ForEach m (A.Literal m (A.List A.Int) (A.RangeLiteral
                 m (intLiteral (-5)) (intLiteral (-2))))))
               (A.Only m (makeSimpleAssign "c" "x"))
    exp = A.Par m A.PlainPar $ A.Spec m (A.Specification m (simpleName "x")
               $ A.Rep m (A.For m (intLiteral (-5)) (makeRange (-5)
                 (-2)) (intLiteral 1)))
               (A.Only m (makeSimpleAssign "c" "x"))                            

testEachRangePass2 :: Test
testEachRangePass2 = TestCase $ testPass "testEachRangePass2" exp transformEachRange orig (return ())
  where
    orig = A.Seq m $ A.Spec m (A.Specification m (simpleName "x") $ A.Rep m
               (A.ForEach m (A.Literal m (A.List A.Int) (A.RangeLiteral m
                 (intLiteral 6) (intLiteral 6)))))
               (A.Only m (makeSimpleAssign "c" "x"))
    exp = A.Seq m $ A.Spec m (A.Specification m (simpleName "x") $ A.Rep m
               (A.For m (intLiteral 6) (makeRange 6 6) (intLiteral 1)))
               (A.Only m (makeSimpleAssign "c" "x"))
               
testEachRangePass3 :: Test
testEachRangePass3 = TestCase $ testPass "testEachRangePass3" exp transformEachRange orig (return ())
  where
    orig = A.Seq m $ A.Spec m (A.Specification m (simpleName "x") $ A.Rep m
               (A.ForEach m (A.Literal m (A.List A.Int) (A.RangeLiteral m
                 (intLiteral 6) (intLiteral 0)))))
               (A.Only m (makeSimpleAssign "c" "x"))
    exp = A.Seq m $ A.Spec m (A.Specification m (simpleName "x") $ A.Rep m
               (A.For m (intLiteral 6) (makeRange 6 0) (intLiteral 1)))
               (A.Only m (makeSimpleAssign "c" "x"))               


-- | Test variable is made unique in a declaration:
testUnique0 :: Test
testUnique0 = TestCase $ testPassWithItemsStateCheck "testUnique0" exp uniquifyAndResolveVars orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m A.Byte) skipP
    exp = mSpecP (tag3 A.Specification DontCare ("newc"@@DontCare) $ A.Declaration m A.Byte) skipP
    check (items,state) 
      = do newcName <- castAssertADI (Map.lookup "newc" items)
           assertNotEqual "testUnique0: Variable was not made unique" "c" (A.nameName newcName)
           assertVarDef "testUnique0: Variable was not recorded" state (A.nameName newcName)
             (tag7 A.NameDef DontCare (A.nameName newcName) "c"
               (A.Declaration m A.Byte) A.Original A.NameUser A.Unplaced)

-- | Tests that two declarations of a variable with the same name are indeed made unique:
testUnique1 :: Test
testUnique1 = TestCase $ testPassWithItemsStateCheck "testUnique1" exp uniquifyAndResolveVars orig (return ()) check
  where
    orig = A.Several m [A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m A.Byte ) skipP,
                        A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m A.Int64 ) skipP]
    exp = mSeveralP [mSpecP (tag3 A.Specification DontCare ("newc0"@@DontCare) $ A.Declaration m A.Byte ) skipP,
                     mSpecP (tag3 A.Specification DontCare ("newc1"@@DontCare) $ A.Declaration m A.Int64 ) skipP]
    check (items,state) 
                = do newc0Name <- castAssertADI (Map.lookup "newc0" items)
                     newc1Name <- castAssertADI (Map.lookup "newc1" items)
                     assertNotEqual "testUnique1: Variable was not made unique" "c" (A.nameName newc0Name)
                     assertNotEqual "testUnique1: Variable was not made unique" "c" (A.nameName newc1Name)
                     assertNotEqual "testUnique1: Variables were not made unique" (A.nameName newc0Name) (A.nameName newc1Name)
                     assertVarDef "testUnique1: Variable was not recorded" state (A.nameName newc0Name)
                       (tag7 A.NameDef DontCare (A.nameName newc0Name) "c"
                         (A.Declaration m A.Byte) A.Original A.NameUser A.Unplaced)
                     assertVarDef "testUnique1: Variable was not recorded" state (A.nameName newc1Name)
                       (tag7 A.NameDef DontCare (A.nameName newc1Name) "c"
                         (A.Declaration m A.Int64) A.Original A.NameUser A.Unplaced)

-- | Tests that the unique pass does resolve the variables that are in scope
testUnique2 :: Test
testUnique2 = TestCase $ testPassWithItemsStateCheck "testUnique2" exp uniquifyAndResolveVars orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m A.Byte ) (A.Only m $ makeSimpleAssign "c" "d")
    exp = mSpecP (tag3 A.Specification DontCare ("newc"@@DontCare) $ A.Declaration m A.Byte )
      (mOnlyP' m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare ("newc"@@DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "d")]))
    check (items,state) = do newcName <- castAssertADI (Map.lookup "newc" items)
                             assertNotEqual "testUnique2: Variable was not made unique" "c" (A.nameName newcName)


testUnique2b :: Test
testUnique2b = TestCase $ testPassWithItemsStateCheck "testUnique2b" exp uniquifyAndResolveVars orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m A.Byte ) $
        A.Several m [(A.Only m $ makeSimpleAssign "c" "d"),(A.Only m $ makeSimpleAssign "c" "e")]
    exp = mSpecP (tag3 A.Specification DontCare ("newc"@@DontCare) $ A.Declaration m A.Byte ) $
      mSeveralP [
        (mOnlyP' m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare ("newc"@@DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "d")]))
        ,(mOnlyP' m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare ("newc"@@DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "e")]))
      ]
    check (items,state) = do newcName <- castAssertADI (Map.lookup "newc" items)
                             assertNotEqual "testUnique2: Variable was not made unique" "c" (A.nameName newcName)


-- | Tests that proc names are recorded, but not made unique (because they might be exported), and not resolved either
testUnique3 :: Test
testUnique3 = TestCase $ testPassWithItemsStateCheck "testUnique3" exp uniquifyAndResolveVars orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (procName "foo") $ A.Proc m (A.PlainSpec, A.Recursive) [] $ Just
      $ A.Skip m) (A.Only m $ A.ProcCall m (procName "foo") [])
    exp = orig
    check (items,state) = assertVarDef "testUnique3: Variable was not recorded" state "foo"
                            (tag7 A.NameDef DontCare "foo" "foo"
                              (A.Proc m (A.PlainSpec, A.Recursive) [] $ Just $
                                A.Skip m) A.Original A.NameUser A.Unplaced)

-- | Tests that parameters are uniquified and resolved:
testUnique4 :: Test
testUnique4 = TestCase $ testPassWithItemsStateCheck "testUnique4" exp uniquifyAndResolveVars orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (procName "foo") $ A.Proc m (A.PlainSpec, A.Recursive) [A.Formal A.ValAbbrev A.Byte $ simpleName "c"] $ Just $ 
      A.ProcCall m (procName "foo") [A.ActualExpression $ exprVariable "c"]) (skipP)
    exp = mSpecP
             (tag3 A.Specification DontCare (procNamePattern "foo") $ tag4 A.Proc DontCare (A.PlainSpec, A.Recursive)
               [tag3 A.Formal A.ValAbbrev A.Byte newc] 
               (bodyPattern newc)
             )
             skipP
    bodyPattern n = (tag3 A.ProcCall DontCare (procNamePattern "foo") 
                      [tag1 A.ActualExpression $ tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare n]
                    )

    newc = Named "newc" DontCare
    check (items,state) 
      = do newcName <- castAssertADI (Map.lookup "newc" items)
           assertNotEqual "testUnique4: Variable was not made unique" "c" (A.nameName newcName)
           assertVarDef "testUnique4: Variable was not recorded" state (A.nameName newcName)
             (tag7 A.NameDef DontCare (A.nameName newcName) "c"
               (A.Declaration m A.Byte) A.ValAbbrev A.NameUser A.Unplaced)
           assertVarDef "testUnique4: Variable was not recorded" state "foo"
             (tag7 A.NameDef DontCare "foo" "foo"
               (tag4 A.Proc DontCare (A.PlainSpec, A.Recursive)
                 [tag3 A.Formal A.ValAbbrev A.Byte newcName] (bodyPattern newcName))
               A.Original A.NameUser A.Unplaced)
           
-- TODO check that doing {int : c; { int: c; } } does give an error
-- TODO check that declaring a new proc with the same name as an old one does give an error


--Easy way to string two passes together; creates a pass-like function that applies the left-hand pass then the right-hand pass.  Associative.
(>>>) :: Pass t -> Pass t -> Pass t
(>>>) f0 f1 = Pass {passCode = passCode f1 <.< passCode f0}

--Normally, process names in Rain are not mangled.  And this should be fine in all cases - but not for the main process (which would
--result in a function called main.  Therefore we must mangle main.  Ideally into a nonce, but for now into ____main

--TODO check recursive main function works

testFindMain0 :: Test
testFindMain0 = TestCase $ testPassWithItemsStateCheck "testFindMain0" exp (uniquifyAndResolveVars >>> findMain) orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (A.Name m "main") $ A.Proc m (A.PlainSpec, A.Recursive) [] (Just $ A.Skip m)) $ A.Several m [] :: A.AST
    exp = mSpecAST (tag3 A.Specification DontCare (tag2 A.Name DontCare ("main"@@DontCare)) $
      tag4 A.Proc DontCare (A.PlainSpec, A.Recursive) ([] :: [A.Formal]) (tag1 A.Skip DontCare)) $ mSeveralAST ([] :: [A.AST])
    check (items,state) 
      = do mainName <- castAssertADI (Map.lookup "main" items)
           assertNotEqual "testFindMain0 A" "main" mainName
           assertEqual "testFindMain0 B" [(mainName, (A.Name m mainName, ProcName))] (csMainLocals state)
           assertVarDef "testFindMain0 C" state mainName
                       (tag7 A.NameDef DontCare mainName "main" DontCare A.Original A.NameUser A.Unplaced)

testFindMain1 :: Test
testFindMain1 = TestCase $ testPassWithStateCheck "testFindMain1" orig (uniquifyAndResolveVars >>> findMain) orig (return ()) check
  where
    orig = A.Spec m (A.Specification m (A.Name m "foo") $ A.Proc m (A.PlainSpec, A.Recursive) [] (Just $ A.Skip m)) $ A.Several m ([] :: [A.AST])
    check state = assertEqual "testFindMain1" [] (csMainLocals state)
    
testFindMain2 :: Test
testFindMain2 = TestCase $ testPassWithItemsStateCheck "testFindMain2" exp (uniquifyAndResolveVars >>> findMain) orig (return ()) check
  where
    inner = A.Spec m (A.Specification m (A.Name m "foo") $ A.Proc m (A.PlainSpec, A.Recursive) [] (Just $ A.Skip m)) $
               A.Several m ([] :: [A.AST])
    orig = A.Spec m (A.Specification m (A.Name m "main") $ A.Proc m (A.PlainSpec, A.Recursive) [] (Just $ A.Skip m)) inner
             
    exp = mSpecAST (tag3 A.Specification DontCare (tag2 A.Name DontCare ("main"@@DontCare)) $
      tag4 A.Proc DontCare (A.PlainSpec, A.Recursive) ([] :: [A.Formal]) (tag1 A.Skip DontCare)) (stopCaringPattern m $ mkPattern inner)
    check (items,state) 
      = do mainName <- castAssertADI (Map.lookup "main" items)
           assertNotEqual "testFindMain2 A" "main" mainName
           assertEqual "testFindMain2 B" [(mainName, (A.Name m mainName, ProcName))] (csMainLocals state)

testParamPass :: 
  String              -- ^ The test name
  -> Maybe [A.Formal] -- ^ The parameters of a process\/function to optionally define
  -> [A.Actual]       -- ^ The parameters of the process\/function call 
  -> Maybe [A.Actual] -- ^ The result (or Nothing if failure is expected)
  -> Test

testParamPass testName formals params transParams 
  = case transParams of 
      Just act -> TestList [TestCase $ testPass (testName ++ "/process") (expProc act) performTypeUnification origProc startStateProc,
                            TestCase $ testPass (testName ++ "/function") (expFunc act) performTypeUnification origFunc startStateFunc]
      Nothing -> TestList [TestCase $ testPassShouldFail (testName ++ "/process") performTypeUnification origProc startStateProc,
                           TestCase $ testPassShouldFail (testName ++ "/function") performTypeUnification origFunc startStateFunc]
  where
    startStateProc :: State CompState ()
    startStateProc = do defineName (simpleName "x") $ simpleDefDecl "x" (A.UInt16)
                        case formals of
                          Nothing -> return ()
                          Just formals' -> defineName (procName "foo") $ simpleDef "foo" $ A.Proc m (A.PlainSpec, A.Recursive) formals' (Just $ A.Skip m)
    startStateFunc :: State CompState ()
    startStateFunc = do defineName (simpleName "x") $ simpleDefDecl "x" (A.UInt16)
                        case formals of
                          Nothing -> return ()
                          Just formals' -> defineName (funcName "foo") $ simpleDef "foo" $ A.Function m (A.PlainSpec,A.Recursive) [A.Byte] formals' (Just $ Left $ A.Only m $ A.ExpressionList m [])
    origProc = A.ProcCall m (procName "foo") params
    expProc ps = A.ProcCall m (procName "foo") ps
    origFunc = A.FunctionCall m (funcName "foo") (deActualise params)
    expFunc ps = A.FunctionCall m (funcName "foo") (deActualise ps)
    deActualise :: [A.Actual] -> [A.Expression]
    deActualise = map deActualise'
    deActualise' :: A.Actual -> A.Expression
    deActualise' (A.ActualVariable v) = A.ExprVariable m v
    deActualise' (A.ActualExpression e) = e

-- | Test no-params:
testParamPass0 :: Test
testParamPass0 = testParamPass "testParamPass0" (Just []) [] (Just [])

-- | Test param of right type:
testParamPass1 :: Test
testParamPass1 = testParamPass "testParamPass1" 
  (Just [A.Formal A.ValAbbrev A.UInt16 (simpleName "p0")]) 
  [A.ActualVariable (variable "x")]
  (Just [A.ActualVariable (variable "x")])

-- testParamPass2 was no longer applicable

-- | Test invalid implicit down-cast:
testParamPass3 :: Test
testParamPass3 = testParamPass "testParamPass3"
  (Just [A.Formal A.ValAbbrev A.Int8 (simpleName "p0"),A.Formal A.ValAbbrev A.UInt32 (simpleName "p1")])
  [A.ActualVariable (variable "x"),A.ActualVariable (variable "x")]
  Nothing

-- | Test explicit down-cast:
testParamPass4 :: Test
testParamPass4 = testParamPass "testParamPass4"
  (Just [A.Formal A.ValAbbrev A.Int8 (simpleName "p0"),A.Formal A.ValAbbrev A.UInt16 (simpleName "p1")])
  [A.ActualExpression $ A.Conversion m A.DefaultConversion A.Int8 (exprVariable "x"),A.ActualVariable (variable "x")]
  (Just [A.ActualExpression $ A.Conversion m A.DefaultConversion A.Int8 (exprVariable "x"),
         A.ActualVariable (variable "x")])

-- | Test too few parameters:
testParamPass5 :: Test
testParamPass5 = testParamPass "testParamPass5"
  (Just [A.Formal A.ValAbbrev A.UInt16 (simpleName "p0")])
  []
  Nothing

-- | Test too many parameters:
testParamPass6 :: Test
testParamPass6 = testParamPass "testParamPass6"
  (Just [A.Formal A.ValAbbrev A.UInt16 (simpleName "p0")])
  [A.ActualVariable (variable "x"),A.ActualVariable (variable "x")]
  Nothing

-- | Test unknown process:
testParamPass7 :: Test
testParamPass7 = testParamPass "testParamPass7"
  Nothing
  [A.ActualVariable (variable "x"),A.ActualVariable (variable "x")]
  Nothing

-- | Test calling something that is not a process:
testParamPass8 :: Test
testParamPass8 = TestList [TestCase $ testPassShouldFail "testParamPass8/process" performTypeUnification origProc (startState'),
                           TestCase $ testPassShouldFail "testParamPass8/function" performTypeUnification origFunc (startState')]
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "x") $ simpleDefDecl "x" (A.UInt16)
    origProc = A.ProcCall m (procName "x") []
    origFunc = A.FunctionCall m (funcName "x") []

--TODO test passing in channel ends

-- | Transform an example list
testRangeRepPass0 :: Test
testRangeRepPass0 = TestCase $ testPass "testRangeRepPass0" exp transformRangeRep orig (return())
  where
    orig = A.Literal m (A.List A.Int) $ A.RangeLiteral m (intLiteral 0) (intLiteral 1)
    exp = mLiteral (A.List A.Int) $ mArrayListLiteral $ mSpecE
        (mSpecification ("repIndex"@@DontCare) (mRep $ mFor (intLiteral 0) (makeRange 0 1) (intLiteral 1)))
      (mOnlyE $ mExprVariable $ mVariable $ "repIndex"@@DontCare)

--TODO consider/test pulling up the definitions of variables involved in return statements in functions

{-
-- | Test a fairly standard function:
testCheckFunction0 :: Test
testCheckFunction0 = TestCase $ testPass "testCheckFunction0" orig checkFunction orig (return ())
  where
    orig = A.Specification m (procName "id") $
        A.Function m A.PlainSpec [A.Byte] [A.Formal A.ValAbbrev A.Byte (simpleName "x")] $ Right
          (A.Seq m $ A.Several m [A.Only m $ A.Assign m [variable "id"] $ A.ExpressionList m [exprVariable "x"]])

-- | Test a function without a return as the final statement:
testCheckFunction1 :: Test
testCheckFunction1 = TestCase $ testPassShouldFail "testCheckFunction1" checkFunction orig (return ())
  where
    orig = A.Specification m (procName "brokenid") $
        A.Function m A.PlainSpec [A.Byte] [A.Formal A.ValAbbrev A.Byte (simpleName "x")] $
          (Right $ A.Seq m $ A.Several m [])
-}
testPullUpParDecl0 :: Test
testPullUpParDecl0 = TestCase $ testPass "testPullUpParDecl0" orig pullUpParDeclarations orig (return ())
  where
    orig = A.Par m A.PlainPar (A.Several m [])

testPullUpParDecl1 :: Test
testPullUpParDecl1 = TestCase $ testPass "testPullUpParDecl1" exp pullUpParDeclarations orig (return ())
  where
    orig = A.Par m A.PlainPar $
      A.Spec m (A.Specification m (simpleName "x") $ A.Declaration m A.Int) (A.Several m [])
    exp = A.Seq m $ A.Spec m (A.Specification m (simpleName "x") $ A.Declaration m A.Int) (A.Only m $ A.Par m A.PlainPar $ A.Several m [])

testPullUpParDecl2 :: Test
testPullUpParDecl2 = TestCase $ testPass "testPullUpParDecl2" exp pullUpParDeclarations orig (return ())
  where
    orig = A.Par m A.PlainPar $
      A.Spec m (A.Specification m (simpleName "x") $ A.Declaration m A.Int) $
      A.Spec m (A.Specification m (simpleName "y") $ A.Declaration m A.Byte) $
      (A.Several m [])
    exp = A.Seq m $ A.Spec m (A.Specification m (simpleName "x") $ A.Declaration m A.Int)
                  $ A.Spec m (A.Specification m (simpleName "y") $ A.Declaration m A.Byte)
                    (A.Only m $ A.Par m A.PlainPar $ A.Several m [])

---Returns the list of tests:
tests :: Test
tests = TestLabel "RainPassesTest" $ TestList
 [
   testEachRangePass0
   ,testEachRangePass1
   ,testEachRangePass2
   ,testEachRangePass3
   ,testUnique0
   ,testUnique1
   ,testUnique2
   ,testUnique2b
   ,testUnique3
   ,testUnique4
   ,testFindMain0
   ,testFindMain1
   ,testFindMain2
   ,testParamPass0
   ,testParamPass1
   ,testParamPass3
   ,testParamPass4
   ,testParamPass5
   ,testParamPass6
   ,testParamPass7
   ,testParamPass8
   ,testRangeRepPass0
--   ,testCheckFunction0
--   ,testCheckFunction1
   ,testPullUpParDecl0
   ,testPullUpParDecl1
   ,testPullUpParDecl2
 ]


