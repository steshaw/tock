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

-- | Contains test for various shared passes.
module PassTest (tests) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Metadata
import Pattern
import SimplifyComms
import SimplifyExprs
import TagAST
import TestUtils
import TreeUtils
import Utils

m :: Meta
m = emptyMeta

-- | An expression list containing a single value of 0.
valof0 :: A.Structured A.ExpressionList
valof0 = A.Only m $ A.ExpressionList m [intLiteral 0]

-- | An expression list containing variables with the two given names.
valofTwo :: String -> String -> A.Structured A.ExpressionList
valofTwo a b = A.Only m $ A.ExpressionList m [exprVariable a,exprVariable b]

-- | Looks up an item from the Items, and attempts to cast it.  Fails (via assertions) if
-- either the item is not found, or if the cast is invalid.
assertGetItemCast  :: Typeable t => String -> Items -> IO t
assertGetItemCast k kv 
  = case (Map.lookup k kv) of
      Nothing -> (assertFailure "Internal error; expected item not present") >> return (undefined)
      Just (ADI v) -> case (cast v) of
        Just v' -> return v'
        Nothing -> (assertFailure $ "Wrong type when casting in assertGetItemCast for key: " ++ k) >> return (undefined)

-- | Given a body, returns a function spec:
singleParamFunc :: A.Structured A.ExpressionList -> A.Specification
singleParamFunc body = A.Specification m (simpleName "foo") (A.Function m A.PlainSpec [A.Int] [A.Formal A.ValAbbrev A.Byte (simpleName "param0")] (Left body))

singleParamFuncProc :: A.Process -> A.Specification
singleParamFuncProc body = A.Specification m (simpleName "foo") (A.Function m A.PlainSpec [A.Int] [A.Formal A.ValAbbrev A.Byte (simpleName "param0")] (Right body))

-- | Returns the expected body of the single parameter process (when the function had valof0 as a body)
singleParamBodyExp :: Pattern -- ^ to match: A.Process
singleParamBodyExp = tag2 A.Seq DontCare $ mOnlyP $
                         tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "ret0" DontCare)] $ tag2 A.ExpressionList DontCare [intLiteral 0]

-- | Returns the expected specification type of the single parameter process
singleParamSpecExp :: Pattern -> Pattern -- ^ to match: A.SpecType
singleParamSpecExp body = tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Byte (simpleName "param0"), tag3 A.Formal A.Abbrev A.Int (Named "ret0" DontCare)] body

-- | Tests a function with a single return, and a single parameter.
testFunctionsToProcs0 :: Test
testFunctionsToProcs0 = TestCase $ testPassWithItemsStateCheck "testFunctionsToProcs0" exp (functionsToProcs orig) (return ()) check
  where
    orig = singleParamFunc valof0
    exp = tag3 A.Specification DontCare (simpleName "foo") procSpec
    procSpec = singleParamSpecExp singleParamBodyExp
                             --check return parameters were defined:
    check (items,state) = do ret0 <- ((assertGetItemCast "ret0" items) :: IO A.Name)                        
                             assertVarDef "testFunctionsToProcs0" state (A.nameName ret0) $
                               tag7 A.NameDef DontCare (A.nameName ret0) (A.nameName ret0) A.VariableName (A.Declaration m A.Int) A.Abbrev A.Unplaced
                             --check proc was defined:
                             assertVarDef "testFunctionsToProcs0" state "foo" $
                               tag7 A.NameDef DontCare ("foo") ("foo") A.ProcName procSpec A.Original A.Unplaced
                             --check csFunctionReturns was changed:
                             assertEqual "testFunctionsToProcs0" (Just [A.Int]) (Map.lookup "foo" (csFunctionReturns state)) 

-- | Tests a function with multiple returns, and multiple parameters.
testFunctionsToProcs1 :: Test
testFunctionsToProcs1 = TestCase $ testPassWithItemsStateCheck "testFunctionsToProcs1 A" exp (functionsToProcs orig) (return ()) check
  where
    orig = A.Specification m (simpleName "foo") (A.Function m A.PlainSpec [A.Int,A.Real32] 
      [A.Formal A.ValAbbrev A.Byte (simpleName "param0"),A.Formal A.Abbrev A.Real32 (simpleName "param1")] (Left $ valofTwo "param0" "param1"))
    exp = tag3 A.Specification DontCare (simpleName "foo") procBody
    procBody = tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Byte (simpleName "param0"), 
                                                 tag3 A.Formal A.Abbrev A.Real32 (simpleName "param1"),
                                                 tag3 A.Formal A.Abbrev A.Int (Named "ret0" DontCare),
                                                 tag3 A.Formal A.Abbrev A.Real32 (Named "ret1" DontCare)] $
                 tag2 A.Seq DontCare $
                   mOnlyP $ 
                     tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "ret0" DontCare),tag2 A.Variable DontCare (Named "ret1" DontCare)] $ 
                       tag2 A.ExpressionList DontCare [exprVariable "param0",exprVariable "param1"]
                             --check return parameters were defined:
    check (items,state) = do ret0 <- ((assertGetItemCast "ret0" items) :: IO A.Name)
                             ret1 <- ((assertGetItemCast "ret1" items) :: IO A.Name)
                             assertVarDef "testFunctionsToProcs1 B" state (A.nameName ret0) $
                               tag7 A.NameDef DontCare (A.nameName ret0) (A.nameName ret0) A.VariableName (A.Declaration m A.Int) A.Abbrev A.Unplaced
                             assertVarDef "testFunctionsToProcs1 C" state (A.nameName ret1) $
                               tag7 A.NameDef DontCare (A.nameName ret1) (A.nameName ret1) A.VariableName (A.Declaration m A.Real32) A.Abbrev A.Unplaced
                             --check proc was defined:
                             assertVarDef "testFunctionsToProcs1 D" state "foo" $
                               tag7 A.NameDef DontCare ("foo") ("foo") A.ProcName procBody A.Original A.Unplaced
                             --check csFunctionReturns was changed:
                             assertEqual "testFunctionsToProcs1 E" (Just [A.Int,A.Real32]) (Map.lookup "foo" (csFunctionReturns state)) 

-- | Tests a function that contains a function.
-- Currently I have chosen to put DontCare for the body of the function as stored in the NameDef.
-- This behaviour is not too important, and may change at a later date.
testFunctionsToProcs2 :: Test
testFunctionsToProcs2 = TestCase $ testPassWithItemsStateCheck "testFunctionsToProcs2 A" exp (functionsToProcs orig) (return ()) check
  where
    orig = A.Specification m (simpleName "fooOuter") (A.Function m A.PlainSpec [A.Int] [A.Formal A.ValAbbrev A.Byte (simpleName "paramOuter0")] $ Left $
      A.Spec m (singleParamFunc valof0) valof0)
    exp = tag3 A.Specification DontCare (simpleName "fooOuter") procBodyOuter
    procHeader body = tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Byte (simpleName "paramOuter0"), tag3 A.Formal A.Abbrev A.Int (Named "retOuter0" DontCare)] body
    procBodyOuter = procHeader $
                 tag2 A.Seq DontCare $                 
                   mSpecP (tag3 A.Specification DontCare (simpleName "foo") (singleParamSpecExp singleParamBodyExp)) $
                     mOnlyP $ 
                       tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "retOuter0" DontCare)] $ tag2 A.ExpressionList DontCare [intLiteral 0]


                             --check return parameters were defined:
    check (items,state) = do retOuter0 <- ((assertGetItemCast "retOuter0" items) :: IO A.Name)
                             ret0 <- ((assertGetItemCast "ret0" items) :: IO A.Name)
                             assertVarDef "testFunctionsToProcs2 B" state (A.nameName ret0) $
                               tag7 A.NameDef DontCare (A.nameName ret0) (A.nameName ret0) A.VariableName (A.Declaration m A.Int) A.Abbrev A.Unplaced
                             assertVarDef "testFunctionsToProcs2 C" state (A.nameName retOuter0) $
                               tag7 A.NameDef DontCare (A.nameName retOuter0) (A.nameName retOuter0) A.VariableName (A.Declaration m A.Int) A.Abbrev A.Unplaced
                             --check proc was defined:
                             assertVarDef "testFunctionsToProcs2 D" state "foo" $
                               tag7 A.NameDef DontCare ("foo") ("foo") A.ProcName (singleParamSpecExp DontCare) A.Original A.Unplaced
                             assertVarDef "testFunctionsToProcs2 E" state "fooOuter" $
                               tag7 A.NameDef DontCare ("fooOuter") ("fooOuter") A.ProcName (procHeader DontCare) A.Original A.Unplaced
                             --check csFunctionReturns was changed:
                             assertEqual "testFunctionsToProcs2 F" (Just [A.Int]) (Map.lookup "foo" (csFunctionReturns state)) 
                             assertEqual "testFunctionsToProcs2 G" (Just [A.Int]) (Map.lookup "fooOuter" (csFunctionReturns state)) 

-- | Tests a function with a single return, and a single parameter, with a Process body
testFunctionsToProcs3 :: Test
testFunctionsToProcs3 = TestCase $ testPassWithItemsStateCheck "testFunctionsToProcs3" exp (functionsToProcs orig) (return ()) check
  where
    orig = singleParamFuncProc $ A.Seq m $ A.Only m $ A.Assign m [variable "foo"] $ A.ExpressionList m [intLiteral 0]
    exp = tag3 A.Specification DontCare (simpleName "foo") procSpec
    procSpec = singleParamSpecExp singleParamBodyExp
                             --check return parameters were defined:
    check (items,state) = do ret0 <- ((assertGetItemCast "ret0" items) :: IO A.Name)                        
                             assertVarDef "testFunctionsToProcs3" state (A.nameName ret0) $
                               tag7 A.NameDef DontCare (A.nameName ret0) (A.nameName ret0) A.VariableName (A.Declaration m A.Int) A.Abbrev A.Unplaced
                             --check proc was defined:
                             assertVarDef "testFunctionsToProcs3" state "foo" $
                               tag7 A.NameDef DontCare ("foo") ("foo") A.ProcName procSpec A.Original A.Unplaced
                             --check csFunctionReturns was changed:
                             assertEqual "testFunctionsToProcs3" (Just [A.Int]) (Map.lookup "foo" (csFunctionReturns state)) 

-- | Tests a function with multiple returns, and multiple parameters.
testFunctionsToProcs4 :: Test
testFunctionsToProcs4 = TestCase $ testPassWithItemsStateCheck "testFunctionsToProcs4 A" exp (functionsToProcs orig) (return ()) check
  where
    orig = A.Specification m (simpleName "foo") (A.Function m A.PlainSpec [A.Int,A.Real32] 
      [A.Formal A.ValAbbrev A.Byte (simpleName "param0"),A.Formal A.Abbrev A.Real32 (simpleName "param1")] $
        Right $ A.Seq m $ A.Only m $ A.Assign m [variable "foo"] $ A.ExpressionList m [exprVariable "param0", exprVariable "param1"])
    exp = tag3 A.Specification DontCare (simpleName "foo") procBody
    procBody = tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Byte (simpleName "param0"), 
                                                 tag3 A.Formal A.Abbrev A.Real32 (simpleName "param1"),
                                                 tag3 A.Formal A.Abbrev A.Int (Named "ret0" DontCare),
                                                 tag3 A.Formal A.Abbrev A.Real32 (Named "ret1" DontCare)] $
                 tag2 A.Seq DontCare $
                   mOnlyP $ 
                     tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "ret0" DontCare),tag2 A.Variable DontCare (Named "ret1" DontCare)] $ 
                       tag2 A.ExpressionList DontCare [exprVariable "param0",exprVariable "param1"]
                             --check return parameters were defined:
    check (items,state) = do ret0 <- ((assertGetItemCast "ret0" items) :: IO A.Name)
                             ret1 <- ((assertGetItemCast "ret1" items) :: IO A.Name)
                             assertVarDef "testFunctionsToProcs4 B" state (A.nameName ret0) $
                               tag7 A.NameDef DontCare (A.nameName ret0) (A.nameName ret0) A.VariableName (A.Declaration m A.Int) A.Abbrev A.Unplaced
                             assertVarDef "testFunctionsToProcs4 C" state (A.nameName ret1) $
                               tag7 A.NameDef DontCare (A.nameName ret1) (A.nameName ret1) A.VariableName (A.Declaration m A.Real32) A.Abbrev A.Unplaced
                             --check proc was defined:
                             assertVarDef "testFunctionsToProcs4 D" state "foo" $
                               tag7 A.NameDef DontCare ("foo") ("foo") A.ProcName procBody A.Original A.Unplaced
                             --check csFunctionReturns was changed:
                             assertEqual "testFunctionsToProcs4 E" (Just [A.Int,A.Real32]) (Map.lookup "foo" (csFunctionReturns state)) 


skipP :: A.Structured A.Process
skipP = A.Only m (A.Skip m)

-- | Tests that a simple constructor (with no expression, nor function call) gets converted into the appropriate initialisation code
testTransformConstr0 :: Test
testTransformConstr0 = TestCase $ testPass "transformConstr0" exp (transformConstr orig) startState
  where
    startState :: State CompState ()
    startState = defineConst "x" A.Int (intLiteral 42)

    orig = A.Spec m (A.Specification m (simpleName "arr") $ A.IsExpr m A.ValAbbrev (A.Array [dimension 10] A.Int) $ A.ExprConstr m $
      A.RepConstr m undefined (A.For m (simpleName "x") (intLiteral 0) (intLiteral 10)) (exprVariable "x")
      ) skipP
    exp = nameAndStopCaringPattern "indexVar" "i" $ mkPattern exp'
    exp' = A.Spec m (A.Specification m (simpleName "arr") (A.Declaration m (A.Array [dimension 10] A.Int))) $ 
      A.ProcThen m 
      (A.Seq m $ A.Spec m (A.Specification m (simpleName "i") (A.Declaration m A.Int)) $
          A.Several m [A.Only m $ A.Assign m [variable "i"] $ A.ExpressionList m [intLiteral 0],
            A.Rep m (A.For m (simpleName "x") (intLiteral 0) (intLiteral 10)) $ A.Only m $ A.Seq m $ A.Several m
            [A.Only m $ A.Assign m [A.SubscriptedVariable m (A.Subscript m A.NoCheck $ exprVariable "i") (variable "arr")] $ A.ExpressionList m [exprVariable "x"],
            A.Only m $ A.Assign m [variable "i"] $ A.ExpressionList m [A.Dyadic m A.Plus (exprVariable "i") (intLiteral 1)]]
          ]
      )
      skipP


testOutExprs :: Test
testOutExprs = TestList
 [
  -- Test outputting from an expression:
  TestCase $ testPassWithItemsStateCheck "testOutExprs 0" 
    (tag2 A.Seq DontCare $ (abbr "temp_var" A.Int (eXM 1))
      (mOnlyP $ tag3 A.Output emptyMeta chan
        [tag2 A.OutExpression emptyMeta (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare (Named "temp_var" DontCare)))])
    )
    (outExprs $ 
      A.Output emptyMeta chan [outXM 1]
    )
    (defineName (xName) $ simpleDefDecl "x" A.Int)
    (checkTempVarTypes "testOutExprs 0" [("temp_var", A.Int)])

  -- Test outputting from a variable already:
  ,TestCase $ testPass "testOutExprs 1" 
    (tag2 A.Seq DontCare $
      (mOnlyP $ tag3 A.Output emptyMeta chan
        [outX])
    )
    (outExprs $ 
      A.Output emptyMeta chan [outX]
    )
    (return ())
    
  -- Test outputting from multiple output items:
  ,TestCase $ testPassWithItemsStateCheck "testOutExprs 2"
    (tag2 A.Seq DontCare $ (abbr "temp_var0" A.Byte (eXM 1)) $ (abbr "temp_var1" A.Int (intLiteral 2))
      (mOnlyP $ tag3 A.Output emptyMeta chan
        [tag2 A.OutExpression emptyMeta (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare (Named "temp_var0" DontCare)))
        ,mkPattern outX
        ,tag2 A.OutExpression emptyMeta (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare (Named "temp_var1" DontCare)))
        ]
      )
    )
    (outExprs $
      A.Output emptyMeta chan [outXM 1,outX,A.OutExpression emptyMeta $ intLiteral 2]
    )
    (defineName (xName) $ simpleDefDecl "x" A.Byte)
    (checkTempVarTypes "testOutExprs 2" [("temp_var0", A.Byte),("temp_var1", A.Int)])
    
  -- Test an OutCounted
  ,TestCase $ testPassWithItemsStateCheck "testOutExprs 3"
    (tag2 A.Seq DontCare $ (abbr "temp_var" A.Byte (eXM 1))
      (mOnlyP $ tag3 A.Output emptyMeta chan
        [tag3 A.OutCounted emptyMeta 
          (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare (Named "temp_var0" DontCare)))
          (exprVariable "x")
        ]
      )
    )
    (outExprs $
      A.Output emptyMeta chan [A.OutCounted emptyMeta (eXM 1) (exprVariable "x")]
    )
    (defineName (xName) $ simpleDefDecl "x" A.Byte)
    (checkTempVarTypes "testOutExprs 3" [("temp_var", A.Byte)])

  -- Test that OutputCase is also processed:
  ,TestCase $ testPassWithItemsStateCheck "testOutExprs 4" 
    (tag2 A.Seq DontCare $ (abbr "temp_var" A.Int (eXM 1))
      (mOnlyP $ tag4 A.OutputCase emptyMeta chan (simpleName "foo")
        [tag2 A.OutExpression emptyMeta (tag2 A.ExprVariable DontCare (tag2 A.Variable DontCare (Named "temp_var" DontCare)))])
    )
    (outExprs $ 
      A.OutputCase emptyMeta chan (simpleName "foo") [outXM 1]
    )
    (defineName (xName) $ simpleDefDecl "x" A.Int)
    (checkTempVarTypes "testOutExprs 3" [("temp_var", A.Int)])

  -- Test that an empty outputcase works okay:

  ,TestCase $ testPass "testOutExprs 5" 
    (tag2 A.Seq DontCare $
      (mOnlyP $ A.OutputCase emptyMeta chan (simpleName "foo") [])
    )
    (outExprs $ 
      A.OutputCase emptyMeta chan (simpleName "foo") []
    )
    (return ())

 ]
 where
   outX = A.OutExpression emptyMeta $ exprVariable "x"
   outXM n = A.OutExpression emptyMeta $ eXM n
   eXM n = buildExpr $ Dy (Var "x") A.Minus (Lit $ intLiteral n)
  
   abbr key t e = mSpecP
     (tag3 A.Specification DontCare (Named key DontCare) $ tag4 A.IsExpr DontCare A.ValAbbrev t e)
 
   chan = variable "c"
   xName = simpleName "x"
   

testInputCase :: Test
testInputCase = TestList
  [
   -- Input that only involves tags:
   {-
   The idea is to transform:
     c ? CASE
       a0
         --Process p0
   into:
     SEQ
       INT tag:
       SEQ
         c ? tag
         CASE tag
           a0
             --Process p0
   -}
   TestCase $ testPass "testInputCase 0"     
       (tag2 A.Seq DontCare $ 
          mSpecP (tag3 A.Specification DontCare (Named "tag" DontCare) $ mDeclaration A.Int) $
          mSeveralP
         [mOnlyP $ tag3 A.Input DontCare c $ tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]
         ,mOnlyP $ tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $
           mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 0] p0
         ]
     )
     (transformInputCase $ 
       A.Input emptyMeta c $ A.InputCase emptyMeta $ A.Only emptyMeta $ A.Variant emptyMeta a0 [] p0
     )
     (defineMyProtocol >> defineC)
     
   -- Input that involves multiple tags and multiple inputs:
   {-
   The idea is to transform:
     c ? CASE
       a0
         --Process p0
       c1 ; z
         --Process p1
       b2 ; x ; y
         --Process p2
   into:
     SEQ
       INT tag:
       SEQ
         c ? tag
         CASE tag
           a0
             --Process p0
           c1
             SEQ
               c ? z
               --Process p1
           b2
             SEQ
               c ? x ; y
               --Process p2
   -}
   ,TestCase $ testPass "testInputCase 1"
       (tag2 A.Seq DontCare $ 
          mSpecP (tag3 A.Specification DontCare (Named "tag" DontCare) $ mDeclaration A.Int) $
          mSeveralP
         [mOnlyP $ tag3 A.Input DontCare c $ tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]
         ,mOnlyP $ tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $ mSeveralO
          [mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 0] p0
          ,mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 2] $
            tag2 A.Seq DontCare $ mSeveralP
              [mOnlyP $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta z],mOnlyP p1]
          ,mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 1] $
            tag2 A.Seq DontCare $ mSeveralP
              [mOnlyP $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta x,A.InVariable emptyMeta y],mOnlyP p2]
          ]
         ]
     )
     (transformInputCase $ 
       A.Input emptyMeta c $ A.InputCase emptyMeta $ A.Several emptyMeta 
         [A.Only emptyMeta $ A.Variant emptyMeta a0 [] p0
         ,A.Only emptyMeta $ A.Variant emptyMeta c1 [A.InVariable emptyMeta z] p1
         ,A.Only emptyMeta $ A.Variant emptyMeta b2 [A.InVariable emptyMeta x,A.InVariable emptyMeta y] p2
         ]
     )
     (defineMyProtocol >> defineC)

   -- Input that involves multiple tags and multiple inputs and specs (sheesh!):
   {-
   The idea is to transform:
     c ? CASE
       a0
         --Process p0
       INT z:
       c1 ; z
         --Process p1
       INT x:
       INT y:
       b2 ; x ; y
         --Process p2
   into:
     SEQ
       INT tag:
       SEQ
         c ? tag
         CASE tag
           a0
             --Process p0
           INT z:
           c1
             SEQ
               c ? z
               --Process p1
           INT x:
           INT y:
           b2
             SEQ
               c ? x ; y
               --Process p2
   -}
   ,TestCase $ testPass "testInputCase 2"
       (tag2 A.Seq DontCare $ 
          mSpecP (tag3 A.Specification DontCare (Named "tag" DontCare) $ mDeclaration A.Int) $
          mSeveralP
         [mOnlyP $ tag3 A.Input DontCare c $ tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]
         ,mOnlyP $ tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $ mSeveralO
          [mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 0] p0
          ,specIntPatt "z" $ mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 2] $
            tag2 A.Seq DontCare $ mSeveralP
              [mOnlyP $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta z],mOnlyP p1]
          ,specIntPatt "x" $ specIntPatt "y" $ mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 1] $
            tag2 A.Seq DontCare $ mSeveralP
              [mOnlyP $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta x,A.InVariable emptyMeta y],mOnlyP p2]
          ]
         ]
     )
     (transformInputCase $ 
       A.Input emptyMeta c $ A.InputCase emptyMeta $ A.Several emptyMeta 
         [A.Only emptyMeta $ A.Variant emptyMeta a0 [] p0
         ,specInt "z" $ A.Only emptyMeta $ A.Variant emptyMeta c1 [A.InVariable emptyMeta z] p1
         ,specInt "x" $ specInt "y" $ A.Only emptyMeta $ A.Variant emptyMeta b2 [A.InVariable emptyMeta x,A.InVariable emptyMeta y] p2
         ]
     )
     (defineMyProtocol >> defineC)
     
     --TODO test alt guards

   -- Input that only involves tags:
   {-
   The idea is to transform:
     ALT
       c ? CASE
         a0
           --Process p0
   into:
     ALT
       INT tag:
       c ? tag
         CASE tag
           a0
             --Process p0
   -}
   ,TestCase $ testPass "testInputCase 100"
       (tag3 A.Alt DontCare False $ 
          mSpecA (tag3 A.Specification DontCare (Named "tag" DontCare) $ mDeclaration A.Int) $
          mOnlyA $ tag4 A.Alternative DontCare c
            (tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]) $
          tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $
           mOnlyO $ tag3 A.Option DontCare [intLiteralPattern 0] p0
     )
     (transformInputCase $ 
       A.Alt emptyMeta False $ A.Only emptyMeta $ A.Alternative emptyMeta c 
        (A.InputCase emptyMeta $ A.Only emptyMeta $ A.Variant emptyMeta a0 [] p0)
        (A.Skip emptyMeta)
     )
     (defineMyProtocol >> defineC)

  ]
  where
    -- Various distinct simple processes:
    p0 = A.Skip emptyMeta
    p1 = A.Seq emptyMeta (A.Several emptyMeta [])
    p2 = A.Stop emptyMeta
    c = variable "c"
    x = variable "x"
    y = variable "y"
    z = variable "z"
    a0 = simpleName "a0"
    b2 = simpleName "b2"
    c1 = simpleName "c1"
    defineMyProtocol :: CSM m => m ()
    defineMyProtocol = defineName (simpleName "prot") $ A.NameDef emptyMeta "prot" "prot" A.ProtocolName
      (A.ProtocolCase emptyMeta [(a0,[]),(b2,[A.Int,A.Int]),(c1,[A.Int])])
      A.Original A.Unplaced
    defineC :: CSM m => m ()
    defineC = defineName (simpleName "c") $ simpleDefDecl "c" (A.Chan A.DirUnknown (A.ChanAttributes False False) (A.UserProtocol $ simpleName "prot"))
    
    specInt s = A.Spec emptyMeta (A.Specification emptyMeta (simpleName s) $ A.Declaration emptyMeta A.Int)
    specIntPatt s = mSpecA' emptyMeta (A.Specification emptyMeta (simpleName s) $ A.Declaration emptyMeta A.Int)

testTransformProtocolInput :: Test
testTransformProtocolInput = TestList
  [
    TestCase $ testPass "testTransformProtocolInput0"
      (seqItems [ii0])
      (transformProtocolInput $ seqItems [ii0])
      (return ())
   ,TestCase $ testPass "testTransformProtocolInput1"
      (A.Seq emptyMeta $ A.Several emptyMeta $ map onlySingle [ii0, ii1, ii2])
      (transformProtocolInput $ seqItems [ii0, ii1, ii2])
      (return ())
   
   ,TestCase $ testPass "testTransformProtocolInput2"
      (A.Alt emptyMeta False $ onlySingleAlt ii0)
      (transformProtocolInput $ A.Alt emptyMeta False $ onlySingleAlt ii0)
      (return ())

   ,TestCase $ testPass "testTransformProtocolInput3"
      (A.Alt emptyMeta True $ A.Only emptyMeta $ A.Alternative emptyMeta (variable "c") (A.InputSimple emptyMeta [ii0]) $
        A.Seq emptyMeta $ A.Several emptyMeta $ onlySingle ii1 : [A.Only emptyMeta $ A.Skip emptyMeta])
      (transformProtocolInput $ A.Alt emptyMeta True $ A.Only emptyMeta $ altItems [ii0, ii1])
      (return ())

   ,TestCase $ testPass "testTransformProtocolInput4"
      (A.Alt emptyMeta False $ A.Only emptyMeta $ A.Alternative emptyMeta (variable "c") (A.InputSimple emptyMeta [ii0]) $
        A.Seq emptyMeta $ A.Several emptyMeta $ map onlySingle [ii1,ii2] ++ [A.Only emptyMeta $ A.Skip emptyMeta])
      (transformProtocolInput $ A.Alt emptyMeta False $ A.Only emptyMeta $ altItems [ii0, ii1, ii2])
      (return ())
  ]
  where
   ii0 = A.InVariable emptyMeta (variable "x")
   ii1 = A.InCounted emptyMeta (variable "y") (variable "z")
   ii2 = A.InVariable emptyMeta (variable "a")
  
   onlySingle = A.Only emptyMeta . A.Input emptyMeta (variable "c") . A.InputSimple emptyMeta . singleton
   onlySingleAlt = A.Only emptyMeta . flip (A.Alternative emptyMeta (variable "c")) (A.Skip emptyMeta) . A.InputSimple emptyMeta . singleton
   seqItems = A.Input emptyMeta (variable "c") . A.InputSimple emptyMeta
   altItems = flip (A.Alternative emptyMeta (variable "c")) (A.Skip emptyMeta) . A.InputSimple emptyMeta


testPullRepCounts :: Test
testPullRepCounts = TestList
  [
    testUnchanged 0 $ A.Par emptyMeta A.PlainPar
   ,testUnchanged 1 $ A.Par emptyMeta A.PriPar
   ,testUnchanged 2 $ A.Alt emptyMeta False
   ,testUnchanged 3 $ A.Alt emptyMeta True
   ,testUnchanged 4 $ A.If emptyMeta
   
   ,TestCase $ testPass "testPullRepCounts 5"
     (nameAndStopCaringPattern "nonce" "nonce" $ mkPattern $ A.Seq emptyMeta $
       A.Spec emptyMeta (A.Specification emptyMeta (simpleName "nonce") (A.IsExpr emptyMeta A.ValAbbrev A.Int $ intLiteral 6)) $
         A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (exprVariable "nonce")) $ A.Several emptyMeta [])
       
     (pullRepCounts $ A.Seq emptyMeta $ A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (intLiteral 6)) $ A.Several emptyMeta [])
     (return ())

   ,TestCase $ testPass "testPullRepCounts 6"
     (nameAndStopCaringPattern "nonce" "nonce" $ nameAndStopCaringPattern "nonce2" "nonce2" $ mkPattern $ A.Seq emptyMeta $
       A.Spec emptyMeta (A.Specification emptyMeta (simpleName "nonce") (A.IsExpr emptyMeta A.ValAbbrev A.Int $ intLiteral 6)) $
         A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (exprVariable "nonce")) $
           A.Spec emptyMeta (A.Specification emptyMeta (simpleName "nonce2") (A.IsExpr emptyMeta A.ValAbbrev A.Int $ intLiteral 8)) $
             A.Rep emptyMeta (A.For emptyMeta (simpleName "j") (intLiteral 0) (exprVariable "nonce2")) $ A.Several emptyMeta [])
       
     (pullRepCounts $ A.Seq emptyMeta $ A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (intLiteral 6)) $
        A.Rep emptyMeta (A.For emptyMeta (simpleName "j") (intLiteral 0) (intLiteral 8)) $ A.Several emptyMeta [])
     (return ())
  ]
  where
    testUnchanged :: Data a => Int -> (A.Structured a -> A.Process) -> Test
    testUnchanged n f = TestCase $ testPass
      ("testPullRepCounts/testUnchanged " ++ show n)
      code
      (pullRepCounts code)
      (return ())
      where 
        code = (f $ A.Rep emptyMeta (A.For emptyMeta (simpleName "i") (intLiteral 0) (intLiteral 5)) $ A.Several emptyMeta [])


--Returns the list of tests:
tests :: Test
tests = TestLabel "PassTest" $ TestList
 [
   testFunctionsToProcs0
   ,testFunctionsToProcs1
   ,testFunctionsToProcs2
   ,testFunctionsToProcs3
   ,testFunctionsToProcs4
   ,testInputCase
   ,testOutExprs
   ,testPullRepCounts
   ,testTransformConstr0
   ,testTransformProtocolInput
 ]


