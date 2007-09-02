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

module RainPassTest (tests) where

import Test.HUnit hiding (State)
import Control.Monad.State as CSM
import qualified Data.Map as Map
import qualified AST as A
import TestUtil
import Pattern
import TreeUtil
import RainPasses
import CompState
import Control.Monad.Error (runErrorT)
import Control.Monad.Identity
import Types
import Pass
import Data.Generics
import Utils
import Errors

simpleDef :: String -> A.SpecType -> A.NameDef
simpleDef n sp = A.NameDef {A.ndMeta = m, A.ndName = n, A.ndOrigName = n, A.ndNameType = A.VariableName,
                            A.ndType = sp, A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}

simpleDefDecl :: String -> A.Type -> A.NameDef
simpleDefDecl n t = simpleDef n (A.Declaration m t)

simpleDefPattern :: String -> A.AbbrevMode -> Pattern -> Pattern
simpleDefPattern n am sp = tag7 A.NameDef DontCare n n A.VariableName sp am A.Unplaced

skipP :: A.Structured
skipP = A.OnlyP m (A.Skip m)

castAssertADI :: (Typeable b) => Maybe AnyDataItem -> IO b
castAssertADI x = case (castADI x) of
  Just y -> return y
  Nothing -> dieInternal "Pattern successfully matched but did not find item afterwards"

testEachPass0 :: Test
testEachPass0 = testPassWithItemsStateCheck "testEachPass0" exp (transformEach orig) startState' check
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
                     --ValAbbrev because we are abbreviating an expression:
                     (tag4 A.Is DontCare A.ValAbbrev A.Byte 
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
    
    --Need to also check the names were recorded properly in CompState, so that later passes will work properly:
    check :: (Items,CompState) -> Assertion
    check (items,st) = 
      do case castADI (Map.lookup "indexVar" items) of
           Just indexVarName -> assertVarDef "testEachPass0" st (A.nameName indexVarName) 
             (simpleDefPattern (A.nameName indexVarName) A.Original (tag2 A.Declaration DontCare A.Int64)) 
           Nothing -> assertFailure "testEachPass0: Internal error, indexVar not found"
         case castADI (Map.lookup "listVarName" items) of
           Just listVarName -> assertVarDef "testEachPass0" st (A.nameName listVarName)
             (simpleDefPattern (A.nameName listVarName) A.ValAbbrev (tag4 A.IsExpr DontCare A.ValAbbrev (A.Array [A.Dimension 1] A.Byte) (makeLiteralStringPattern "1") ))
           Nothing -> assertFailure "testEachPass0: Internal error, listVarName not found"

testEachPass1 :: Test
testEachPass1 = testPassWithItemsStateCheck "testEachPass0" exp (transformEach orig) startState' check
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
    --Need to also check the names were recorded properly in CompState, so that later passes will work properly:
    check :: (Items,CompState) -> Assertion
    check (items,st) = 
      do case castADI (Map.lookup "indexVar" items) of
           Just indexVarName -> assertVarDef "testEachPass1" st (A.nameName indexVarName) 
             (simpleDefPattern (A.nameName indexVarName) A.Original (tag2 A.Declaration DontCare A.Int64)) 
           Nothing -> assertFailure "testEachPass1: Internal error, indexVar not found"

testEachRangePass0 :: Test
testEachRangePass0 = testPass "testEachRangePass0" exp (transformEachRange orig) (return ())
  where
    orig = A.Par m A.PlainPar $ A.Rep m
               (A.ForEach m (simpleName "x") (A.ExprConstr m (A.RangeConstr m (intLiteral 0) (intLiteral 9))))
               (A.OnlyP m (makeSimpleAssign "c" "x"))
    exp = A.Par m A.PlainPar $ A.Rep m
               (A.For m (simpleName "x") (intLiteral 0) (intLiteral 10))
               (A.OnlyP m (makeSimpleAssign "c" "x"))
               
testEachRangePass1 :: Test
testEachRangePass1 = testPass "testEachRangePass1" exp (transformEachRange orig) (return ())
  where
    orig = A.Par m A.PlainPar $ A.Rep m
               (A.ForEach m (simpleName "x") (A.ExprConstr m (A.RangeConstr m (intLiteral (-5)) (intLiteral (-2)))))
               (A.OnlyP m (makeSimpleAssign "c" "x"))
    exp = A.Par m A.PlainPar $ A.Rep m
               (A.For m (simpleName "x") (intLiteral (-5)) (intLiteral 4))
               (A.OnlyP m (makeSimpleAssign "c" "x"))                            

testEachRangePass2 :: Test
testEachRangePass2 = testPass "testEachRangePass2" exp (transformEachRange orig) (return ())
  where
    orig = A.Seq m $ A.Rep m
               (A.ForEach m (simpleName "x") (A.ExprConstr m (A.RangeConstr m (intLiteral 6) (intLiteral 6))))
               (A.OnlyP m (makeSimpleAssign "c" "x"))
    exp = A.Seq m $ A.Rep m
               (A.For m (simpleName "x") (intLiteral 6) (intLiteral 1))
               (A.OnlyP m (makeSimpleAssign "c" "x"))
               
testEachRangePass3 :: Test
testEachRangePass3 = testPass "testEachRangePass3" exp (transformEachRange orig) (return ())
  where
    orig = A.Seq m $ A.Rep m
               (A.ForEach m (simpleName "x") (A.ExprConstr m (A.RangeConstr m (intLiteral 6) (intLiteral 0))))
               (A.OnlyP m (makeSimpleAssign "c" "x"))
    exp = A.Seq m $ A.Rep m
               (A.For m (simpleName "x") (intLiteral 6) (intLiteral (-5)))
               (A.OnlyP m (makeSimpleAssign "c" "x"))               


-- | Test variable is made unique in a declaration:
testUnique0 :: Test
testUnique0 = testPassWithItemsStateCheck "testUnique0" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) skipP
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte) skipP
    check (items,state) 
      = do newcName <- castAssertADI (Map.lookup "newc" items)
           assertNotEqual "testUnique0: Variable was not made unique" "c" (A.nameName newcName)
           assertVarDef "testUnique0: Variable was not recorded" state (A.nameName newcName)
             (tag7 A.NameDef DontCare (A.nameName newcName) "c" A.VariableName (A.Declaration m A.Byte) A.Original A.Unplaced)

-- | Tests that two declarations of a variable with the same name are indeed made unique:
testUnique1 :: Test
testUnique1 = testPassWithItemsStateCheck "testUnique1" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Several m [A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) skipP,
                        A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Int64) skipP]
    exp = tag2 A.Several m [tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc0" DontCare) $ A.Declaration m $ A.Byte) skipP,
                            tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc1" DontCare) $ A.Declaration m $ A.Int64) skipP]
    check (items,state) 
                = do newc0Name <- castAssertADI (Map.lookup "newc0" items)
                     newc1Name <- castAssertADI (Map.lookup "newc1" items)
                     assertNotEqual "testUnique1: Variable was not made unique" "c" (A.nameName newc0Name)
                     assertNotEqual "testUnique1: Variable was not made unique" "c" (A.nameName newc1Name)
                     assertNotEqual "testUnique1: Variables were not made unique" (A.nameName newc0Name) (A.nameName newc1Name)
                     assertVarDef "testUnique1: Variable was not recorded" state (A.nameName newc0Name)
                       (tag7 A.NameDef DontCare (A.nameName newc0Name) "c" A.VariableName (A.Declaration m A.Byte) A.Original A.Unplaced)
                     assertVarDef "testUnique1: Variable was not recorded" state (A.nameName newc1Name)
                       (tag7 A.NameDef DontCare (A.nameName newc1Name) "c" A.VariableName (A.Declaration m A.Int64) A.Original A.Unplaced)

-- | Tests that the unique pass does resolve the variables that are in scope
testUnique2 :: Test
testUnique2 = testPassWithItemsStateCheck "testUnique2" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) (A.OnlyP m $ makeSimpleAssign "c" "d")
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte) 
      (tag2 A.OnlyP m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "newc" DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "d")]))
    check (items,state) = do newcName <- castAssertADI (Map.lookup "newc" items)
                             assertNotEqual "testUnique2: Variable was not made unique" "c" (A.nameName newcName)


testUnique2b :: Test
testUnique2b = testPassWithItemsStateCheck "testUnique2b" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (simpleName "c") $ A.Declaration m $ A.Byte) $
    	A.Several m [(A.OnlyP m $ makeSimpleAssign "c" "d"),(A.OnlyP m $ makeSimpleAssign "c" "e")]
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "newc" DontCare) $ A.Declaration m $ A.Byte) $
      tag2 A.Several DontCare [
        (tag2 A.OnlyP m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "newc" DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "d")]))
        ,(tag2 A.OnlyP m $ tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "newc" DontCare)] (tag2 A.ExpressionList DontCare [(exprVariable "e")]))
      ]
    check (items,state) = do newcName <- castAssertADI (Map.lookup "newc" items)
                             assertNotEqual "testUnique2: Variable was not made unique" "c" (A.nameName newcName)


-- | Tests that proc names are recorded, but not made unique (because they might be exported), and not resolved either
testUnique3 :: Test
testUnique3 = testPassWithItemsStateCheck "testUnique3" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (procName "foo") $ A.Proc m A.PlainSpec [] $ A.Skip m) (A.OnlyP m $ A.ProcCall m (procName "foo") [])
    exp = orig
    check (items,state) = assertVarDef "testUnique3: Variable was not recorded" state "foo"
                            (tag7 A.NameDef DontCare "foo" "foo" A.ProcName (A.Proc m A.PlainSpec [] $ A.Skip m) A.Original A.Unplaced)

-- | Tests that parameters are uniquified and resolved:
testUnique4 :: Test
testUnique4 = testPassWithItemsStateCheck "testUnique4" exp (uniquifyAndResolveVars orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (procName "foo") $ A.Proc m A.PlainSpec [A.Formal A.ValAbbrev A.Byte $ simpleName "c"] $ 
      A.ProcCall m (procName "foo") [A.ActualExpression A.Byte $ exprVariable "c"]) (skipP)
    exp = tag3 A.Spec DontCare 
             (tag3 A.Specification DontCare (procNamePattern "foo") $ tag4 A.Proc DontCare A.PlainSpec 
               [tag3 A.Formal A.ValAbbrev A.Byte newc] 
               (bodyPattern newc)
             )
             skipP
    bodyPattern n = (tag3 A.ProcCall DontCare (procNamePattern "foo") 
                      [tag2 A.ActualExpression A.Byte $ tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare n]
                    )

    newc = Named "newc" DontCare
    check (items,state) 
      = do newcName <- castAssertADI (Map.lookup "newc" items)
           assertNotEqual "testUnique4: Variable was not made unique" "c" (A.nameName newcName)
           assertVarDef "testUnique4: Variable was not recorded" state (A.nameName newcName)
             (tag7 A.NameDef DontCare (A.nameName newcName) "c" A.VariableName (A.Declaration m A.Byte) A.ValAbbrev A.Unplaced)
           assertVarDef "testUnique4: Variable was not recorded" state "foo"
             (tag7 A.NameDef DontCare "foo" "foo" A.ProcName (tag4 A.Proc DontCare A.PlainSpec 
               [tag3 A.Formal A.ValAbbrev A.Byte newcName] (bodyPattern newcName)) A.Original A.Unplaced)
           



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

--Easy way to string two passes together; creates a pass-like function that applies the left-hand pass then the right-hand pass.  Associative.
(>>>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
(>>>) f0 f1 x = (f0 x) >>= f1

--Normally, process names in Rain are not mangled.  And this should be fine in all cases - but not for the main process (which would
--result in a function called main.  Therefore we must mangle main.  Ideally into a nonce, but for now into ____main

--TODO check recursive main function works

testFindMain0 :: Test
testFindMain0 = testPassWithItemsStateCheck "testFindMain0" exp ((uniquifyAndResolveVars >>> findMain) orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (A.Name m A.ProcName "main") $ A.Proc m A.PlainSpec [] (A.Skip m)) $ A.Several m []
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (tag3 A.Name DontCare A.ProcName (Named "main" DontCare)) $
      tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal]) (tag1 A.Skip DontCare)) $ tag2 A.Several DontCare ([] :: [A.Structured])
    check (items,state) 
      = do mainName <- castAssertADI (Map.lookup "main" items)
           assertNotEqual "testFindMain0 A" "main" mainName
           assertEqual "testFindMain0 B" [(mainName,(A.Name m A.ProcName mainName))] (csMainLocals state)
           assertVarDef "testFindMain0 C" state mainName
                       (tag7 A.NameDef DontCare mainName "main" A.ProcName DontCare A.Original A.Unplaced)

testFindMain1 :: Test
testFindMain1 = testPassWithStateCheck "testFindMain1" orig ((uniquifyAndResolveVars >>> findMain) orig) (return ()) check
  where
    orig = A.Spec m (A.Specification m (A.Name m A.ProcName "foo") $ A.Proc m A.PlainSpec [] (A.Skip m)) $ A.Several m []
    check state = assertEqual "testFindMain1" [] (csMainLocals state)
    
testFindMain2 :: Test
testFindMain2 = testPassWithItemsStateCheck "testFindMain2" exp ((uniquifyAndResolveVars >>> findMain) orig) (return ()) check
  where
    inner = A.Spec m (A.Specification m (A.Name m A.ProcName "foo") $ A.Proc m A.PlainSpec [] (A.Skip m)) $
               A.Several m []
    orig = A.Spec m (A.Specification m (A.Name m A.ProcName "main") $ A.Proc m A.PlainSpec [] (A.Skip m)) inner
             
    exp = tag3 A.Spec DontCare (tag3 A.Specification DontCare (tag3 A.Name DontCare A.ProcName (Named "main" DontCare)) $
      tag4 A.Proc DontCare A.PlainSpec ([] :: [A.Formal]) (tag1 A.Skip DontCare)) (stopCaringPattern m $ mkPattern inner)
    check (items,state) 
      = do mainName <- castAssertADI (Map.lookup "main" items)
           assertNotEqual "testFindMain2 A" "main" mainName
           assertEqual "testFindMain2 B" [(mainName,(A.Name m A.ProcName mainName))] (csMainLocals state)

testParamPass :: 
  String              -- ^ The test name
  -> Maybe [A.Formal] -- ^ The parameters of a process\/function to optionally define
  -> [A.Actual]       -- ^ The parameters of the process\/function call 
  -> Maybe [A.Actual] -- ^ The result (or Nothing if failure is expected)
  -> Test

testParamPass testName formals params transParams 
  = case transParams of 
      Just act -> TestList [testPass (testName ++ "/process") (expProc act) (matchParamPass origProc) startStateProc,
                            testPass (testName ++ "/function") (expFunc act) (matchParamPass origFunc) startStateFunc]
      Nothing -> TestList [testPassShouldFail (testName ++ "/process") (matchParamPass origProc) startStateProc,
                           testPassShouldFail (testName ++ "/function") (matchParamPass origFunc) startStateFunc]
  where
    startStateProc :: State CompState ()
    startStateProc = do defineName (simpleName "x") $ simpleDefDecl "x" (A.UInt16)
                        case formals of
                          Nothing -> return ()
                          Just formals' -> defineName (procName "foo") $ simpleDef "foo" $ A.Proc m A.PlainSpec formals' (A.Skip m)
    startStateFunc :: State CompState ()
    startStateFunc = do defineName (simpleName "x") $ simpleDefDecl "x" (A.UInt16)
                        case formals of
                          Nothing -> return ()
                          Just formals' -> defineName (funcName "foo") $ simpleDef "foo" $ A.Function m A.PlainSpec [A.Byte] formals' (A.OnlyP m $ A.Skip m)
    origProc = A.ProcCall m (procName "foo") params
    expProc ps = A.ProcCall m (procName "foo") ps
    origFunc = A.FunctionCall m (funcName "foo") (deActualise params)
    expFunc ps = A.FunctionCall m (funcName "foo") (deActualise ps)
    deActualise :: [A.Actual] -> [A.Expression]
    deActualise = map deActualise'
    deActualise' :: A.Actual -> A.Expression
    deActualise' (A.ActualVariable _ _ v) = A.ExprVariable m v
    deActualise' (A.ActualExpression _ e) = e

-- | Test no-params:
testParamPass0 :: Test
testParamPass0 = testParamPass "testParamPass0" (Just []) [] (Just [])

-- | Test param of right type:
testParamPass1 :: Test
testParamPass1 = testParamPass "testParamPass1" 
  (Just [A.Formal A.ValAbbrev A.UInt16 (simpleName "p0")]) 
  [A.ActualVariable A.Original A.Any (variable "x")]
  (Just [A.ActualVariable A.ValAbbrev A.UInt16 (variable "x")])

-- | Test up-casts:
testParamPass2 :: Test
testParamPass2 = testParamPass "testParamPass2"
  (Just [A.Formal A.ValAbbrev A.Int32 (simpleName "p0"),A.Formal A.ValAbbrev A.UInt32 (simpleName "p1")])
  [A.ActualVariable A.Original A.Any (variable "x"),A.ActualVariable A.Original A.Any (variable "x")]
  (Just [A.ActualExpression A.Int32 $ A.Conversion m A.DefaultConversion A.Int32 (exprVariable "x"),
         A.ActualExpression A.UInt32 $ A.Conversion m A.DefaultConversion A.UInt32 (exprVariable "x")])

-- | Test invalid implicit down-cast:
testParamPass3 :: Test
testParamPass3 = testParamPass "testParamPass3"
  (Just [A.Formal A.ValAbbrev A.Int8 (simpleName "p0"),A.Formal A.ValAbbrev A.UInt32 (simpleName "p1")])
  [A.ActualVariable A.Original A.Any (variable "x"),A.ActualVariable A.Original A.Any (variable "x")]
  Nothing

-- | Test explicit down-cast:
testParamPass4 :: Test
testParamPass4 = testParamPass "testParamPass4"
  (Just [A.Formal A.ValAbbrev A.Int8 (simpleName "p0"),A.Formal A.ValAbbrev A.UInt16 (simpleName "p1")])
  [A.ActualExpression A.Int8 $ A.Conversion m A.DefaultConversion A.Int8 (exprVariable "x"),A.ActualVariable A.Original A.Any (variable "x")]
  (Just [A.ActualExpression A.Int8 $ A.Conversion m A.DefaultConversion A.Int8 (exprVariable "x"),
         A.ActualVariable A.ValAbbrev A.UInt16 (variable "x")])

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
  [A.ActualVariable A.Original A.Any (variable "x"),A.ActualVariable A.Original A.Any (variable "x")]
  Nothing

-- | Test unknown process:
testParamPass7 :: Test
testParamPass7 = testParamPass "testParamPass7"
  Nothing
  [A.ActualVariable A.Original A.Any (variable "x"),A.ActualVariable A.Original A.Any (variable "x")]
  Nothing

-- | Test calling something that is not a process:
testParamPass8 :: Test
testParamPass8 = TestList [testPassShouldFail "testParamPass8/process" (matchParamPass origProc) (startState'),
                           testPassShouldFail "testParamPass8/function" (matchParamPass origFunc) (startState')]
  where
    startState' :: State CompState ()
    startState' = do defineName (simpleName "x") $ simpleDefDecl "x" (A.UInt16)
    origProc = A.ProcCall m (procName "x") []
    origFunc = A.FunctionCall m (funcName "x") []

--TODO test passing in channel ends

-- | Transform an example list
testRangeRepPass0 :: Test
testRangeRepPass0 = testPass "testRangeRepPass0" exp (transformRangeRep orig) (return())
  where
    orig = A.ExprConstr m $ A.RangeConstr m (intLiteral 0) (intLiteral 1)
    exp = tag2 A.ExprConstr DontCare $ tag3 A.RepConstr DontCare (tag4 A.For DontCare (Named "repIndex" DontCare) (intLiteral 0) (intLiteral 2)) 
      (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare $ Named "repIndex" DontCare)

-- | Lists with negative counts should be turned into an empty literal list
testRangeRepPass1 :: Test
testRangeRepPass1 = testPass "testRangeRepPass1" exp (transformRangeRep orig) (return())
  where
    orig = A.ExprConstr m $ A.RangeConstr m (intLiteral 1) (intLiteral 0)
    exp = A.Literal m (A.Array [A.Dimension 0] A.Int) $ A.ArrayLiteral m []


---Returns the list of tests:
tests :: Test
tests = TestList
 [
   testEachPass0
   ,testEachPass1
   ,testEachRangePass0
   ,testEachRangePass1
   ,testEachRangePass2
   ,testEachRangePass3
   ,testUnique0
   ,testUnique1
   ,testUnique2
   ,testUnique2b
   ,testUnique3
   ,testUnique4
   ,testRecordInfNames0
   ,testRecordInfNames1
   ,testRecordInfNames2
   ,testRecordInfNames3
   ,testFindMain0
   ,testFindMain1
   ,testFindMain2
   ,testParamPass0
   ,testParamPass1
   ,testParamPass2
   ,testParamPass3
   ,testParamPass4
   ,testParamPass5
   ,testParamPass6
   ,testParamPass7
   ,testParamPass8
   ,testRangeRepPass0
   ,testRangeRepPass1
 ]


