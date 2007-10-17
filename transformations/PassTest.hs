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

module PassTest (tests) where

import Control.Monad.Identity
import Data.Generics
import qualified Data.Map as Map
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Metadata
import Pattern
import SimplifyComms
import SimplifyExprs
import TestUtil
import TreeUtil

valof0 :: A.Structured 
valof0 = A.OnlyEL m $ A.ExpressionList m [intLiteral 0]

valofTwo :: String -> String -> A.Structured
valofTwo a b = A.OnlyEL m $ A.ExpressionList m [exprVariable a,exprVariable b]

assertGetItemCast  :: Typeable t => String -> Items -> IO t
assertGetItemCast k kv 
  = case (Map.lookup k kv) of
      Nothing -> (assertFailure "Internal error; expected item not present") >> return (undefined)
      Just (ADI v) -> case (cast v) of
        Just v' -> return v'
        Nothing -> (assertFailure $ "Wrong type when casting in assertGetItemCast for key: " ++ k) >> return (undefined)

-- Given a body, returns a function spec:
singleParamFunc :: A.Structured-> A.Specification
singleParamFunc body = A.Specification m (simpleName "foo") (A.Function m A.PlainSpec [A.Int] [A.Formal A.ValAbbrev A.Byte (simpleName "param0")] body)

-- Returns the expected body of the single parameter process (when the function had valof0 as a body)
singleParamBodyExp :: Pattern --to match: A.Process
singleParamBodyExp = tag2 A.Seq DontCare $
                       tag2 A.OnlyP DontCare $ 
                         tag3 A.Assign DontCare [tag2 A.Variable DontCare (Named "ret0" DontCare)] $ tag2 A.ExpressionList DontCare [intLiteral 0]

-- Returns the expected specification type of the single parameter process
singleParamSpecExp :: Pattern -> Pattern --to match: A.SpecType
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
      [A.Formal A.ValAbbrev A.Byte (simpleName "param0"),A.Formal A.Abbrev A.Real32 (simpleName "param1")] (valofTwo "param0" "param1"))
    exp = tag3 A.Specification DontCare (simpleName "foo") procBody
    procBody = tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Byte (simpleName "param0"), 
                                                 tag3 A.Formal A.Abbrev A.Real32 (simpleName "param1"),
                                                 tag3 A.Formal A.Abbrev A.Int (Named "ret0" DontCare),
                                                 tag3 A.Formal A.Abbrev A.Real32 (Named "ret1" DontCare)] $
                 tag2 A.Seq DontCare $
                   tag2 A.OnlyP DontCare $ 
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
    orig = A.Specification m (simpleName "fooOuter") (A.Function m A.PlainSpec [A.Int] [A.Formal A.ValAbbrev A.Byte (simpleName "paramOuter0")] $
      A.Spec m (singleParamFunc valof0) valof0)
    exp = tag3 A.Specification DontCare (simpleName "fooOuter") procBodyOuter
    procHeader body = tag4 A.Proc DontCare A.PlainSpec [tag3 A.Formal A.ValAbbrev A.Byte (simpleName "paramOuter0"), tag3 A.Formal A.Abbrev A.Int (Named "retOuter0" DontCare)] body
    procBodyOuter = procHeader $
                 tag2 A.Seq DontCare $                 
                   tag3 A.Spec DontCare (tag3 A.Specification DontCare (simpleName "foo") (singleParamSpecExp singleParamBodyExp)) $
                     tag2 A.OnlyP DontCare $ 
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

skipP :: A.Structured
skipP = A.OnlyP m (A.Skip m)

-- | Tests that a simple constructor (with no expression, nor function call) gets converted into the appropriate initialisation code
testTransformConstr0 :: Test
testTransformConstr0 = TestCase $ testPass "transformConstr0" exp (transformConstr orig) (return ())
  where
    orig = A.Spec m (A.Specification m (simpleName "arr") $ A.IsExpr m A.ValAbbrev (A.Array [A.Dimension 10] A.Int) $ A.ExprConstr m $
      A.RepConstr m (A.For m (simpleName "x") (intLiteral 0) (intLiteral 10)) (exprVariable "x")
      ) skipP
    exp = nameAndStopCaringPattern "indexVar" "i" $ mkPattern exp'
    exp' = A.Spec m (A.Specification m (simpleName "arr") (A.Declaration m (A.Array [A.Dimension 10] A.Int))) $ 
      A.ProcThen m 
      (A.Seq m $ A.Spec m (A.Specification m (simpleName "i") (A.Declaration m A.Int)) $
          A.Several m [A.OnlyP m $ A.Assign m [variable "i"] $ A.ExpressionList m [intLiteral 0],
            A.Rep m (A.For m (simpleName "x") (intLiteral 0) (intLiteral 10)) $ A.OnlyP m $ A.Seq m $ A.Several m
            [A.OnlyP m $ A.Assign m [A.SubscriptedVariable m (A.Subscript m $ exprVariable "i") (variable "arr")] $ A.ExpressionList m [exprVariable "x"],
            A.OnlyP m $ A.Assign m [variable "i"] $ A.ExpressionList m [A.Dyadic m A.Plus (exprVariable "i") (intLiteral 1)]]
          ]
      )
      skipP


testOutExprs :: Test
testOutExprs = TestList
 [
  -- Test outputting from an expression:
  TestCase $ testPassWithItemsStateCheck "testOutExprs 0" 
    (tag2 A.Seq DontCare $ (abbr "temp_var" A.Int (eXM 1))
      (tag2 A.OnlyP DontCare $ tag3 A.Output emptyMeta chan
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
      (tag2 A.OnlyP DontCare $ tag3 A.Output emptyMeta chan
        [outX])
    )
    (outExprs $ 
      A.Output emptyMeta chan [outX]
    )
    (return ())
    
  -- Test outputting from multiple output items:
  ,TestCase $ testPassWithItemsStateCheck "testOutExprs 2"
    (tag2 A.Seq DontCare $ (abbr "temp_var0" A.Byte (eXM 1)) $ (abbr "temp_var1" A.Int (intLiteral 2))
      (tag2 A.OnlyP DontCare $ tag3 A.Output emptyMeta chan
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
      (tag2 A.OnlyP DontCare $ tag3 A.Output emptyMeta chan
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
      (tag2 A.OnlyP DontCare $ tag4 A.OutputCase emptyMeta chan (simpleName "foo")
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
      (tag2 A.OnlyP DontCare $ A.OutputCase emptyMeta chan (simpleName "foo") [])
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
  
   abbr key t e = tag3 A.Spec DontCare
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
          tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "tag" DontCare) $ tag2 A.Declaration DontCare A.Int) $
          tag2 A.Several DontCare
         [tag2 A.OnlyP DontCare $ tag3 A.Input DontCare c $ tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]
         ,tag2 A.OnlyP DontCare $ tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $
           tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 0] p0
         ]
     )
     (transformInputCase $ 
       A.Input emptyMeta c $ A.InputCase emptyMeta $ A.OnlyV emptyMeta $ A.Variant emptyMeta a0 [] p0
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
          tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "tag" DontCare) $ tag2 A.Declaration DontCare A.Int) $
          tag2 A.Several DontCare
         [tag2 A.OnlyP DontCare $ tag3 A.Input DontCare c $ tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]
         ,tag2 A.OnlyP DontCare $ tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $ tag2 A.Several emptyMeta
          [tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 0] p0
          ,tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 2] $
            tag2 A.Seq DontCare $ tag2 A.Several DontCare
              [tag2 A.OnlyP DontCare $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta z],tag2 A.OnlyP DontCare p1]
          ,tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 1] $
            tag2 A.Seq DontCare $ tag2 A.Several DontCare
              [tag2 A.OnlyP DontCare $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta x,A.InVariable emptyMeta y],tag2 A.OnlyP DontCare p2]
          ]
         ]
     )
     (transformInputCase $ 
       A.Input emptyMeta c $ A.InputCase emptyMeta $ A.Several emptyMeta 
         [A.OnlyV emptyMeta $ A.Variant emptyMeta a0 [] p0
         ,A.OnlyV emptyMeta $ A.Variant emptyMeta c1 [A.InVariable emptyMeta z] p1
         ,A.OnlyV emptyMeta $ A.Variant emptyMeta b2 [A.InVariable emptyMeta x,A.InVariable emptyMeta y] p2
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
          tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "tag" DontCare) $ tag2 A.Declaration DontCare A.Int) $
          tag2 A.Several DontCare
         [tag2 A.OnlyP DontCare $ tag3 A.Input DontCare c $ tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]
         ,tag2 A.OnlyP DontCare $ tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $ tag2 A.Several emptyMeta
          [tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 0] p0
          ,specIntPatt "z" $ tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 2] $
            tag2 A.Seq DontCare $ tag2 A.Several DontCare
              [tag2 A.OnlyP DontCare $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta z],tag2 A.OnlyP DontCare p1]
          ,specIntPatt "x" $ specIntPatt "y" $ tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 1] $
            tag2 A.Seq DontCare $ tag2 A.Several DontCare
              [tag2 A.OnlyP DontCare $ A.Input emptyMeta c $ A.InputSimple emptyMeta [A.InVariable emptyMeta x,A.InVariable emptyMeta y],tag2 A.OnlyP DontCare p2]
          ]
         ]
     )
     (transformInputCase $ 
       A.Input emptyMeta c $ A.InputCase emptyMeta $ A.Several emptyMeta 
         [A.OnlyV emptyMeta $ A.Variant emptyMeta a0 [] p0
         ,specInt "z" $ A.OnlyV emptyMeta $ A.Variant emptyMeta c1 [A.InVariable emptyMeta z] p1
         ,specInt "x" $ specInt "y" $ A.OnlyV emptyMeta $ A.Variant emptyMeta b2 [A.InVariable emptyMeta x,A.InVariable emptyMeta y] p2
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
          tag3 A.Spec DontCare (tag3 A.Specification DontCare (Named "tag" DontCare) $ tag2 A.Declaration DontCare A.Int) $
          tag2 A.OnlyA DontCare $ tag4 A.Alternative DontCare c
            (tag2 A.InputSimple DontCare [tag2 A.InVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)]) $
          tag3 A.Case DontCare (tag2 A.ExprVariable DontCare $ tag2 A.Variable DontCare (Named "tag" DontCare)) $
           tag2 A.OnlyO DontCare $ tag3 A.Option DontCare [intLiteralPattern 0] p0
     )
     (transformInputCase $ 
       A.Alt emptyMeta False $ A.OnlyA emptyMeta $ A.Alternative emptyMeta c 
        (A.InputCase emptyMeta $ A.OnlyV emptyMeta $ A.Variant emptyMeta a0 [] p0)
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
    defineMyProtocol = defineName (simpleName "prot") $ A.NameDef emptyMeta "prot" "prot" A.ProtocolName
      (A.ProtocolCase emptyMeta [(a0,[]),(b2,[A.Int,A.Int]),(c1,[A.Int])])
      A.Original A.Unplaced
    defineC = defineName (simpleName "c") $ simpleDefDecl "c" (A.Chan A.DirUnknown (A.ChanAttributes False False) (A.UserProtocol $ simpleName "prot"))
    
    specInt s = A.Spec emptyMeta (A.Specification emptyMeta (simpleName s) $ A.Declaration emptyMeta A.Int)
    specIntPatt s = tag3 A.Spec emptyMeta (A.Specification emptyMeta (simpleName s) $ A.Declaration emptyMeta A.Int)
                             
--Returns the list of tests:
tests :: Test
tests = TestList
 [
   testFunctionsToProcs0
   ,testFunctionsToProcs1
   ,testFunctionsToProcs2
   ,testInputCase
   ,testOutExprs
   ,testTransformConstr0
 ]


