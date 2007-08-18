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

testEachPass0 :: Assertion
testEachPass0 = do origResult <- (evalStateT (runErrorT (transformEach orig)) startState) 
                   case origResult of
                     Left err -> assertFailure ("testEachPass0; pass failed with: " ++ err)
                     Right origTrans -> assertPatternMatch "testEachPass0" exp origTrans
  where
    startState :: CompState
    startState = execState startState' emptyState
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


testEachPass1 :: Assertion
testEachPass1 = do origResult <- (evalStateT (runErrorT (transformEach orig)) startState)
                   case origResult of
                     Left err -> assertFailure ("testEachPass1; pass failed with: " ++ err)
                     Right origTrans -> assertPatternMatch "testEachPass1" exp origTrans
  where
    startState :: CompState
    startState = execState startState' emptyState
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



--Returns the list of tests:
tests :: Test
tests = TestList
 [
   TestCase $ testEachPass0
   ,TestCase $ testEachPass1
 ]


