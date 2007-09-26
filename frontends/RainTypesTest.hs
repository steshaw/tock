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

module RainTypesTest where

import Test.HUnit hiding (State)
import TestUtil
import RainTypes
import TreeUtil
import Pattern
import qualified AST as A
import CompState
import Control.Monad.State
import Control.Monad.Error
import Data.Generics
import Types
import Pass
import Errors

constantFoldTest :: Test
constantFoldTest = TestList
 [
  foldVar 0 $ Var "x"
  ,foldVar 1 $ Dy (Var "x") A.Plus (lit 0)
  
  ,foldCon 100 (lit 2) (Dy (lit 1) A.Plus (lit 1))  
  ,foldCon 101 (lit 65537) (Dy (lit 2) A.Plus (lit 65535))
  ,foldCon 102 (lit (- two63)) (Dy (lit $ two63 - 1) A.Plus (lit 1))
  
  ,foldCon 110 (Dy (Var "x") A.Plus (lit 2)) (Dy (Var "x") A.Plus (Dy (lit 1) A.Plus (lit 1)))
 ]
 where
   two63 :: Integer
   two63 = 9223372036854775808
 
   foldVar :: Int -> ExprHelper -> Test
   foldVar n e = TestCase $ testPass ("constantFoldTest " ++ show n) (buildExprPattern e) (constantFoldPass $ buildExpr e) state

   foldCon :: Int -> ExprHelper -> ExprHelper -> Test
   foldCon n exp orig = TestCase $ testPass ("constantFoldTest " ++ show n) (buildExprPattern exp) (constantFoldPass $ buildExpr orig) state

   state :: State CompState ()
   state = return ()

   lit :: Integer -> ExprHelper
   lit n = Lit $ int64Literal n

annotateIntTest :: Test
annotateIntTest = TestList
 [
  failSigned (-9223372036854775809)
  ,signed A.Int64 (-9223372036854775808)
  ,signed A.Int64 (-2147483649)
  ,signed A.Int32 (-2147483648)
  ,signed A.Int32 (-32769)
  ,signed A.Int16 (-32768)
  ,signed A.Int16 (-129)
  ,signed A.Int8 (-128)
  ,signed A.Int8 0
  ,signed A.Int8 127
  ,signed A.Int16 128
  ,signed A.Int16 32767
  ,signed A.Int32 32768
  ,signed A.Int32 2147483647
  ,signed A.Int64 2147483648
  ,signed A.Int64 9223372036854775807
  ,failSigned 9223372036854775808
 ]
 where
  signed :: A.Type -> Integer -> Test
  signed t n = TestCase $ testPass ("annotateIntTest: " ++ show n) (tag3 A.Literal DontCare t $ tag2 A.IntLiteral DontCare (show n)) 
    (annnotateIntLiteralTypes $ int64Literal n) (return ())
  failSigned :: Integer -> Test
  failSigned n = TestCase $ testPassShouldFail ("annotateIntTest: " ++ show n) (annnotateIntLiteralTypes $ int64Literal n) (return ())

--TODO add typechecks for expressions involving channels
checkExpressionTest :: Test
checkExpressionTest = TestList
 [
  --Already same types:
  passSame 0 A.Int64 $ Dy (Var "x") A.Plus (Var "x")
  ,passSame 1 A.Byte $ Dy (Var "xu8") A.Plus (Var "xu8")
  
  --Upcasting:
  ,pass 100 A.Int64 (Dy (Var "x") A.Plus (Cast A.Int64 $ Var "xu8")) (Dy (Var "x") A.Plus (Var "xu8"))
  ,pass 101 A.Int32 (Dy (Cast A.Int32 $ Var "x16") A.Plus (Cast A.Int32 $ Var "xu16")) (Dy (Var "x16") A.Plus (Var "xu16"))
  
  --Upcasting a cast:
  ,pass 200 A.Int64 (Dy (Var "x") A.Plus (Cast A.Int64 $ Cast A.Int32 $ Var "xu8")) (Dy (Var "x") A.Plus (Cast A.Int32 $ Var "xu8"))
  
  --Impossible conversions:
  ,fail 300 $ Dy (Var "x") A.Plus (Var "xu64")
  
  --Integer literals:
  ,pass 400 A.Int16 (Dy (Var "x16") A.Plus (Cast A.Int16 $ int A.Int8 100)) (Dy (Var "x16") A.Plus (int A.Int8 100))
  ,pass 401 A.Int16 (Dy (Cast A.Int16 $ Var "x8") A.Plus (int A.Int16 200)) (Dy (Var "x8") A.Plus (int A.Int16 200))
  --This fails because you are trying to add a signed constant to an unsigned integer that cannot be expanded:
  ,fail 402 $ Dy (Var "xu64") A.Plus (int A.Int64 0)
  
  --Monadic integer operations:
  ,passSame 500 A.Int32 (Mon A.MonadicMinus (Var "x32"))
  ,pass 501 A.Int32 (Mon A.MonadicMinus (Cast A.Int32 $ Var "xu16")) (Mon A.MonadicMinus (Var "xu16"))
  ,fail 502 $ Mon A.MonadicMinus (Var "xu64")
  ,pass 503 A.Int64 (Dy (Var "x") A.Plus (Cast A.Int64 $ Mon A.MonadicMinus (Var "x32"))) (Dy (Var "x") A.Plus (Mon A.MonadicMinus (Var "x32")))
  
  --Mis-matched types (integer/boolean):
  ,fail 600 $ Dy (Var "b") A.Plus (Var "x")
  ,fail 601 $ Mon A.MonadicMinus (Var "b")
  ,fail 602 $ Dy (Var "x") A.Or (Var "x")
  ,fail 603 $ Dy (Var "x") A.Eq (Var "b")
  ,fail 604 $ Dy (Var "b") A.Plus (Var "b")
  ,fail 605 $ Dy (Var "b") A.Less (Var "b")  
  
  --Comparisons between different integer types:
  ,pass 700 A.Bool (Dy (Var "x") A.Eq (Cast A.Int64 $ Var "xu8")) (Dy (Var "x") A.Eq (Var "xu8"))
  ,pass 701 A.Bool (Dy (Cast A.Int32 $ Var "x16") A.Less (Cast A.Int32 $ Var "xu16")) (Dy (Var "x16") A.Less (Var "xu16"))
  ,pass 702 A.Bool (Dy (Var "x") A.More (Cast A.Int64 $ Cast A.Int32 $ Var "xu8")) (Dy (Var "x") A.More (Cast A.Int32 $ Var "xu8"))
  ,fail 703 $ Dy (Var "x") A.Less (Var "xu64")
  ,pass 704 A.Bool (Dy (Var "x16") A.NotEq (Cast A.Int16 $ int A.Int8 100)) (Dy (Var "x16") A.NotEq (int A.Int8 100))
  ,pass 705 A.Bool (Dy (Cast A.Int16 $ Var "x8") A.MoreEq (int A.Int16 200)) (Dy (Var "x8") A.MoreEq (int A.Int16 200))

  
  --Booleans (easy!)
  ,passSame 1000 A.Bool $ Mon A.MonadicNot (Var "b")
  ,passSame 1001 A.Bool $ Dy (Var "b") A.Or (Var "b")
  ,passSame 1002 A.Bool $ Dy (Var "b") A.And (Mon A.MonadicNot $ Var "b")
  
  --Comparison (same types):
  ,passSame 1100 A.Bool $ Dy (Var "b") A.Eq (Var "b")
  ,passSame 1101 A.Bool $ Dy (Var "x") A.Eq (Var "x")
  ,passSame 1102 A.Bool $ Dy (Var "xu8") A.NotEq (Var "xu8")
  ,passSame 1103 A.Bool $ Dy (Var "x") A.Less (Var "x")
  ,passSame 1104 A.Bool $ Dy (Dy (Var "x") A.Eq (Var "x")) A.And (Dy (Var "xu8") A.NotEq (Var "xu8"))
  
  --Invalid casts:
  ,fail 2000 $ Cast A.Bool (Var "x")
  ,fail 2001 $ Cast A.Bool (int A.Int8 0)
  ,fail 2002 $ Cast A.Int8 (Var "b")
  ,fail 2003 $ Cast A.Int8 (Var "x")
  ,fail 2004 $ Cast A.Int8 (Var "xu8")
  ,fail 2005 $ Cast A.Byte (Var "x8")
  ,fail 2006 $ Cast A.UInt64 (Var "x8")
    
  --Valid casts:
  ,passSame 2100 A.Bool $ Cast A.Bool (Var "b")
  ,passSame 2101 A.Int64 $ Cast A.Int64 (Var "x")
  ,passSame 2102 A.Int64 $ Cast A.Int64 (Var "x8")
  ,passSame 2103 A.Int64 $ Cast A.Int64 (Var "xu8")
  ,passSame 2104 A.Int64 $ Cast A.Int64 $ Cast A.Int32 $ Cast A.UInt16 $ Var "xu8"  
  ,passSame 2105 A.UInt64 $ Cast A.UInt64 (Var "xu8")
  
  --Assignments:
  ,passAssignSame 3000 "x" (Var "x")
  ,passAssignSame 3001 "xu8" (Var "xu8")
  ,passAssignSame 3002 "b" (Var "b")
  ,passAssignSame 3003 "x" $ Dy (Var "x") A.Plus (Var "x")
  ,passAssignSame 3004 "b" $ Dy (Var "x8") A.Eq (Var "x8")
  ,passAssignSame 3005 "x" $ Mon A.MonadicMinus (Var "x")
  ,passAssignSame 3006 "x8" $ int A.Int8 0
  ,passAssignSame 3007 "b" EHTrue

  ,passAssign 3100 "x" (Cast A.Int64 $ Var "xu8") (Var "xu8")
  ,failAssign 3101 "xu8" (Var "x")
  ,failAssign 3102 "x" (Var "b")
  ,failAssign 3103 "b" (Var "x")
  ,failAssign 3104 "x8" (Var "xu8")
  ,failAssign 3105 "xu8" (Var "x8")
  ,passAssign 3106 "x" (Cast A.Int64 $ int A.Int8 0) (int A.Int8 0)
  
  --Conditionals:
  ,passWhileIfSame 4000 $ Var "b"
  ,passWhileIfSame 4001 $ Mon A.MonadicNot $ Var "b"
  ,passWhileIfSame 4002 $ Dy (Var "x") A.Eq (Var "x")
  ,passWhileIfSame 4003 $ EHTrue 
  
  ,failWhileIf 4100 $ Var "x"
  ,failWhileIf 4101 $ Dy (Var "x") A.Plus (Var "x")
  
  --Communication:
  ,testAllCheckCommTypes 5000
  
  --Time types:
  ,fail 6000 $ Dy (Var "t") A.Plus (Var "x")
  ,fail 6001 $ Dy (Var "x") A.Minus (Var "t")
  ,passSame 6002 A.Time $ Dy (Var "t") A.Plus (Var "t")
  ,passSame 6003 A.Time $ Dy (Var "t") A.Minus (Var "t")
  
  ,fail 6100 $ Dy (Var "t") A.Times (Var "t")
  ,passSame 6101 A.Time $ Dy (Var "t") A.Times (Var "x")
  ,passSame 6102 A.Time $ Dy (Var "x") A.Times (Var "t")
  ,pass 6103 A.Time (Dy (Var "t") A.Times (Cast A.Int64 $ Var "xu32")) (Dy (Var "t") A.Times (Var "xu32"))
  ,pass 6104 A.Time (Dy (Cast A.Int64 $ Var "xu32") A.Times (Var "t")) (Dy (Var "xu32") A.Times (Var "t"))
  ,fail 6105 $ Dy (Var "t") A.Times (Var "xu64")
  ,fail 6106 $ Dy (Var "xu64") A.Times (Var "t")
  ,passSame 6107 A.Time $ Dy (Dy (Var "x") A.Times (Var "t")) A.Plus (Dy (Var "t") A.Times (Var "x"))
  ,fail 6108 $ Dy (Dy (Var "x") A.Times (Var "t")) A.Times (Dy (Var "t") A.Times (Var "x"))
  
  ,fail 6200 $ Dy (Var "t") A.Div (Var "t")
  ,fail 6201 $ Dy (Var "x") A.Div (Var "t")
  ,passSame 6202 A.Time $ Dy (Var "t") A.Div (Var "x")
  ,pass 6203 A.Time (Dy (Var "t") A.Div (Cast A.Int64 $ Var "xu32")) (Dy (Var "t") A.Div (Var "xu32"))
  ,fail 6204 $ Dy (Var "t") A.Div (Var "xu64")
  
  ,fail 6300 $ Dy (Var "t") A.Rem (Var "t")
  ,fail 6301 $ Dy (Var "x") A.Rem (Var "t")
  ,fail 6302 $ Dy (Var "t") A.Rem (Var "x")
  
  ,fail 6400 $ Cast A.Time (Var "x")
  ,fail 6401 $ Cast A.Int64 (Var "t")
  
  ,passSame 6500 A.Bool $ Dy (Var "t") A.Eq (Var "t")
  ,passSame 6501 A.Bool $ Dy (Var "t") A.NotEq (Var "t")
  ,passSame 6502 A.Bool $ Dy (Var "t") A.Less (Var "t")
  ,passSame 6503 A.Bool $ Dy (Var "t") A.More (Var "t")
  
  --Now statements:
  ,testPassUntouched 7000 checkGetTimeTypes (A.GetTime m $ variable "t")
  ,TestCase $ testPassShouldFail "checkExpressionTest 7001" (checkGetTimeTypes $ A.GetTime m $ variable "x") state
  
  --Wait statements:
  ,testPassUntouched 7100 checkGetTimeTypes (A.Wait m A.WaitFor $ exprVariable "t")
  ,TestCase $ testPassShouldFail "checkExpressionTest 7101" (checkGetTimeTypes $ A.Wait m A.WaitFor $ exprVariable "x") state
  ,testPassUntouched 7102 checkGetTimeTypes (A.Wait m A.WaitFor $ buildExpr $ Dy (Var "t") A.Plus (Var "t"))

  ,testPassUntouched 7200 checkGetTimeTypes (A.Wait m A.WaitUntil $ exprVariable "t")
  ,TestCase $ testPassShouldFail "checkExpressionTest 7201" (checkGetTimeTypes $ A.Wait m A.WaitUntil $ exprVariable "x") state
  ,testPassUntouched 7202 checkGetTimeTypes (A.Wait m A.WaitUntil $ buildExpr $ Dy (Var "t") A.Plus (Var "t"))
 ]
 where
  testPassUntouched :: Data t => Int -> (t -> PassM t) -> t -> Test
  testPassUntouched n passFunc src = TestCase $ testPass ("checkExpressionTest " ++ show n) (mkPattern src) (passFunc src) state
 
  passAssign :: Int -> String -> ExprHelper -> ExprHelper -> Test
  passAssign n lhs exp src = TestCase $ testPassWithCheck ("checkExpressionTest " ++ show n) 
    (tag3 A.Assign DontCare [variablePattern lhs] $ tag2 A.ExpressionList DontCare [buildExprPattern exp])
    (checkAssignmentTypes $ src')
    state refeed
    where
      src' = A.Assign m [variable lhs] $ A.ExpressionList m [buildExpr src]
    
      refeed :: A.Process -> Assertion
      refeed changed = if (src' /= changed) then testPass ("checkExpressionTest refeed " ++ show n) (mkPattern changed) (checkAssignmentTypes changed) state else return ()
  
  passAssignSame :: Int -> String -> ExprHelper -> Test
  passAssignSame n s e = passAssign n s e e
  
  failAssign :: Int -> String -> ExprHelper -> Test
  failAssign n lhs src = TestCase $ testPassShouldFail ("checkExpressionTest " ++ show n) (checkAssignmentTypes $ A.Assign m [variable lhs] $ A.ExpressionList m [buildExpr src]) state
  
  passWhileIfSame :: Int -> ExprHelper -> Test
  passWhileIfSame n e = passWhileIf n e e
  
  passWhileIf :: Int -> ExprHelper -> ExprHelper -> Test
  passWhileIf n exp src = TestList
    [
      TestCase $ testPass ("checkExpressionTest/if " ++ show n) 
        (tag2 A.If DontCare $ tag2 A.OnlyC DontCare $ tag3 A.Choice DontCare (buildExprPattern exp) (tag1 A.Skip DontCare))
        (checkConditionalTypes $ A.If m $ A.OnlyC m $ A.Choice m (buildExpr src) (A.Skip m))
        state
      ,TestCase $ testPass ("checkExpressionTest/while " ++ show n)
        (tag3 A.While DontCare (buildExprPattern exp) (tag1 A.Skip DontCare))
        (checkConditionalTypes $ A.While m (buildExpr src) (A.Skip m))
        state
    ]
 
  failWhileIf :: Int -> ExprHelper -> Test
  failWhileIf n src = TestList
    [
      TestCase $ testPassShouldFail ("checkExpressionTest/if " ++ show n) 
        (checkConditionalTypes $ A.If m $ A.OnlyC m $ A.Choice m (buildExpr src) (A.Skip m))
        state
      ,TestCase $ testPassShouldFail ("checkExpressionTest/while " ++ show n)
        (checkConditionalTypes $ A.While m (buildExpr src) (A.Skip m))
        state
    ]
    
  --Takes an index, the inner type of the channel and direction with a variable, then the type and variable for the RHS
  --Expects a pass only if the inner type of the channel is the same as the type of the variable, and channel direction is unknown or input
  testCheckCommTypesIn :: Int -> (A.Direction,A.Type,A.Variable) -> (A.Type,A.Variable) -> Test
  testCheckCommTypesIn n (chanDir,chanType,chanVar) (destType,destVar)
    = if (chanType == destType && chanDir /= A.DirOutput)
        then TestCase $ testPass ("testCheckCommTypesIn " ++ show n) (mkPattern st) (checkCommTypes st) state
        else TestCase $ testPassShouldFail ("testCheckCommTypesIn " ++ show n) (checkCommTypes st) state 
      where
        st = A.Input m chanVar $ A.InputSimple m [A.InVariable m destVar]              

  --Takes an index, the inner type of the channel and direction with a variable, then the type and variable for the RHS
  --Expects a pass only if the inner type of the channel is the same as the type of the variable, and channel direction is unknown or input
  testCheckCommTypesInAlt :: Int -> (A.Direction,A.Type,A.Variable) -> (A.Type,A.Variable) -> Test
  testCheckCommTypesInAlt n (chanDir,chanType,chanVar) (destType,destVar)
    = if (chanType == destType && chanDir /= A.DirOutput)
        then TestCase $ testPass ("testCheckCommTypesIn " ++ show n) (mkPattern st) (checkCommTypes st) state
        else TestCase $ testPassShouldFail ("testCheckCommTypesIn " ++ show n) (checkCommTypes st) state 
      where
        st = A.Alt m True $ A.OnlyA m $ A.Alternative m chanVar (A.InputSimple m [A.InVariable m destVar]) $ A.Skip m
 
  --Automatically tests checking inputs and outputs for various combinations of channel type and direction
  testAllCheckCommTypes :: Int -> Test
  testAllCheckCommTypes n = TestList $ map (\(n,f) -> f n) $ zip [n..] $ 
      concat [[\ind -> testCheckCommTypesIn ind c d, \ind -> testCheckCommTypesInAlt ind c d, \ind -> testCheckCommTypesOut ind c d] | c <- chans, d <- vars]
    where
      chans = concatMap allDirs [(A.Int64,variable "c"), (A.Bool,variable "cb"), (A.Byte, variable "cu8")]
      vars = [(A.Bool, variable "b"), (A.Int64, variable "x"), (A.Byte, variable "xu8"), (A.Int16, variable "x16")]
      allDirs :: (A.Type,A.Variable) -> [(A.Direction,A.Type,A.Variable)]
      allDirs (t,v) = 
        [
          (A.DirInput,t,A.DirectedVariable m A.DirInput v)
          ,(A.DirOutput,t,A.DirectedVariable m A.DirOutput v)
          ,(A.DirUnknown,t,v)
        ]        

  --Takes an index, the inner type of the channel and direction with a variable, then the type and variable for the RHS
  --Expects a pass only if the expression type can be cast to the inner type of the channel, and channel direction is unknown or output
  testCheckCommTypesOut :: Int -> (A.Direction,A.Type,A.Variable) -> (A.Type,A.Variable) -> Test
  testCheckCommTypesOut n (chanDir,chanType,chanVar) (srcType,srcVar)
    = if (isImplicitConversionRain srcType chanType && chanDir /= A.DirInput)
        then (if srcType == chanType
                then TestCase $ testPass ("testCheckCommTypesOut " ++ show n) (mkPattern st) (checkCommTypes st) state
                else TestCase $ testPass ("testCheckCommTypesOut " ++ show n) stCast (checkCommTypes st) state
             )
        else TestCase $ testPassShouldFail ("testCheckCommTypesOut " ++ show n) (checkCommTypes st) state 
      where
        st = A.Output m chanVar [A.OutExpression m $ A.ExprVariable m srcVar]
        stCast = tag3 A.Output DontCare chanVar [tag2 A.OutExpression DontCare $ tag4 A.Conversion DontCare A.DefaultConversion chanType $
          A.ExprVariable m srcVar]
        
        
  passSame :: Int -> A.Type -> ExprHelper -> Test
  passSame n t e = pass n t e e
  
  pass :: Int -> A.Type -> ExprHelper -> ExprHelper -> Test
  pass n t exp act = TestCase $ pass' n t (buildExprPattern exp) (buildExpr act)

  --To easily get more tests, we take the result of every successful pass (which must be fine now), and feed it back through
  --the type-checker to check that it is unchanged
  
  pass' :: Int -> A.Type -> Pattern -> A.Expression -> Assertion
  pass' n t exp act = testPassWithCheck ("checkExpressionTest " ++ show n) exp (checkExpressionTypes act) state (check t)   
    where
      check :: A.Type -> A.Expression -> Assertion
      check t e
        = do eot <- errorOrType
             case eot of
               Left err -> assertFailure ("checkExpressionTest " ++ show n ++ " typeOfExpression failed")
               Right t' -> do assertEqual ("checkExpressionTest " ++ show n) t t'
                              --Now feed it through again, to make sure it isn't changed:
                              if (e /= act) then pass' (10000 + n) t (mkPattern e) e else return ()
            where
              errorOrType :: IO (Either ErrorReport A.Type)
              errorOrType = evalStateT (runErrorT $ typeOfExpression e) (execState state emptyState)
  
  
  fail :: Int -> ExprHelper -> Test
  fail n e = TestCase $ testPassShouldFail ("checkExpressionTest " ++ show n) (checkExpressionTypes $ buildExpr e) state
  
  int :: A.Type -> Integer -> ExprHelper
  int t n = Lit $ A.Literal m t $ A.IntLiteral m (show n)

  defVar :: String -> A.Type -> State CompState ()
  defVar n t = defineName (simpleName n) $ simpleDefDecl n t
  
  state :: State CompState ()
  state = do defVar "x" A.Int64
             defVar "b" A.Bool
             defVar "xu8" A.Byte
             defVar "xu16" A.UInt16
             defVar "xu32" A.UInt32
             defVar "xu64" A.UInt64
             defVar "x32" A.Int32
             defVar "x16" A.Int16
             defVar "x8" A.Int8
             defVar "c" $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Int64
             defVar "cu8" $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Byte
             defVar "cb" $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Bool
             defVar "t" $ A.Time
             markRainTest

tests :: Test
tests = TestList
 [
  constantFoldTest
  ,annotateIntTest
  ,checkExpressionTest
 ]
