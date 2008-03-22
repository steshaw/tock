{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

-- | The occam typechecker.
module OccamTypes (checkTypes) where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import CompState
import Errors
import EvalLiterals
import Intrinsics
import Metadata
import Pass
import ShowCode
import Types

-- | A successful check.
ok :: PassM ()
ok = return ()

--{{{  type checks

-- | Are two types the same?
sameType :: A.Type -> A.Type -> PassM Bool
sameType (A.Array (A.Dimension e1 : ds1) t1)
         (A.Array (A.Dimension e2 : ds2) t2)
    =  do n1 <- evalIntExpression e1
          n2 <- evalIntExpression e2
          same <- sameType (A.Array ds1 t1) (A.Array ds2 t2)
          return $ (n1 == n2) && same
sameType (A.Array (A.UnknownDimension : ds1) t1)
         (A.Array (A.UnknownDimension : ds2) t2)
    = sameType (A.Array ds1 t1) (A.Array ds2 t2)
sameType a b = return $ a == b

-- | Check that the second dimension can be used in a context where the first
-- is expected.
isValidDimension :: A.Dimension -> A.Dimension -> PassM Bool
isValidDimension A.UnknownDimension A.UnknownDimension = return True
isValidDimension A.UnknownDimension (A.Dimension _) = return True
isValidDimension (A.Dimension e1) (A.Dimension e2)
    =  do n1 <- evalIntExpression e1
          n2 <- evalIntExpression e2
          return $ n1 == n2
isValidDimension _ _ = return False

-- | Check that the second second of dimensions can be used in a context where
-- the first is expected.
areValidDimensions :: [A.Dimension] -> [A.Dimension] -> PassM Bool
areValidDimensions [] [] = return True
areValidDimensions (d1:ds1) (d2:ds2)
    = do valid <- isValidDimension d1 d2
         if valid
           then areValidDimensions ds1 ds2
           else return False
areValidDimensions _ _ = return False

-- | Check that a type we've inferred matches the type we expected.
checkType :: Meta -> A.Type -> A.Type -> PassM ()
checkType m et rt
    = case (et, rt) of
        ((A.Array ds t), (A.Array ds' t')) ->
          do valid <- areValidDimensions ds ds'
             if valid
               then checkType m t t'
               else bad
        _ ->
          do same <- sameType rt et
             when (not same) $ bad
  where
    bad :: PassM ()
    bad = diePC m $ formatCode "Type mismatch: found %, expected %" rt et

-- | Check a type against a predicate.
checkTypeClass :: (A.Type -> Bool) -> String -> Meta -> A.Type -> PassM ()
checkTypeClass f adjective m rawT
    =  do t <- underlyingType m rawT
          if f t
            then ok
            else diePC m $ formatCode ("Expected " ++ adjective ++ " type; found %") t

-- | Check that a type is numeric.
checkNumeric :: Meta -> A.Type -> PassM ()
checkNumeric = checkTypeClass isNumericType "numeric"

-- | Check that a type is integral.
checkInteger :: Meta -> A.Type -> PassM ()
checkInteger = checkTypeClass isIntegerType "integer"

-- | Check that a type is scalar.
checkScalar :: Meta -> A.Type -> PassM ()
checkScalar = checkTypeClass isScalarType "scalar"

-- | Check that a type is communicable.
checkCommunicable :: Meta -> A.Type -> PassM ()
checkCommunicable = checkTypeClass isCommunicableType "communicable"

-- | Check that a type is a sequence.
checkSequence :: Meta -> A.Type -> PassM ()
checkSequence = checkTypeClass isSequenceType "array or list"

-- | Check that a type is an array.
-- (This also gets used elsewhere where we *know* the argument isn't an array,
-- so that we get a consistent error message.)
checkArray :: Meta -> A.Type -> PassM ()
checkArray m rawT
    =  do t <- underlyingType m rawT
          case t of
            A.Array _ _ -> ok
            _ -> diePC m $ formatCode "Expected array type; found %" t

-- | Check that a type is a list.
-- Return the element type of the list.
checkList :: Meta -> A.Type -> PassM ()
checkList m rawT
    =  do t <- underlyingType m rawT
          case t of
            A.List _ -> ok
            _ -> diePC m $ formatCode "Expected list type; found %" t

-- | Check the type of an expression.
checkExpressionType :: Meta -> A.Type -> A.Expression -> PassM ()
checkExpressionType m et e = typeOfExpression e >>= checkType m et

-- | Check that an expression is of integer type.
checkExpressionInt :: Meta -> A.Expression -> PassM ()
checkExpressionInt m e = checkExpressionType m A.Int e

-- | Check that an expression is of boolean type.
checkExpressionBool :: Meta -> A.Expression -> PassM ()
checkExpressionBool m e = checkExpressionType m A.Bool e

-- | Check the type of a variable.
checkVariableType :: Meta -> A.Type -> A.Variable -> PassM ()
checkVariableType m et v = typeOfVariable v >>= checkType m et

-- | Check that two lists of types match (for example, for parallel
-- assignment).
checkTypeList :: Meta -> [A.Type] -> [A.Type] -> PassM ()
checkTypeList m ets rts
    = sequence_ [checkType m et rt | (et, rt) <- zip ets rts]

--}}}
--{{{  more complex checks

-- | Check that an array literal's length matches its type.
checkArraySize :: Meta -> A.Type -> Int -> PassM ()
checkArraySize m rawT want
    =  do t <- underlyingType m rawT
          case t of
            A.Array (A.UnknownDimension:_) _ -> ok
            A.Array (A.Dimension e:_) _ ->
               do n <- evalIntExpression e
                  when (n /= want) $
                    dieP m $ "Array literal has wrong number of elements: found " ++ show n ++ ", expected " ++ show want
            _ -> checkArray m t

-- | Check that a record field name is valid.
checkRecordField :: Meta -> A.Type -> A.Name -> PassM ()
checkRecordField m t n
    =  do rfs <- recordFields m t
          let validNames = map fst rfs
          when (not $ n `elem` validNames) $
            diePC m $ formatCode "Invalid field name % in record type %" n t

-- | Check that a subscript is being applied to an appropriate type.
checkSubscriptType :: Meta -> A.Subscript -> A.Type -> PassM ()
checkSubscriptType m s rawT
    =  do t <- underlyingType m rawT
          case s of
            -- A record subscript.
            A.SubscriptField m n ->
              checkRecordField m t n
            -- A sequence subscript.
            A.Subscript _ _ _ -> checkSequence m t
            -- An array slice.
            _ -> checkArray m t

-- | Classes of operators.
data OpClass = NumericOp | IntegerOp | ShiftOp | BooleanOp | ComparisonOp
               | ListOp

-- | Figure out the class of a monadic operator.
classifyMOp :: A.MonadicOp -> OpClass
classifyMOp A.MonadicSubtr = NumericOp
classifyMOp A.MonadicMinus = NumericOp
classifyMOp A.MonadicBitNot = IntegerOp
classifyMOp A.MonadicNot = BooleanOp

-- | Figure out the class of a dyadic operator.
classifyOp :: A.DyadicOp -> OpClass
classifyOp A.Add = NumericOp
classifyOp A.Subtr = NumericOp
classifyOp A.Mul = NumericOp
classifyOp A.Div = NumericOp
classifyOp A.Rem = NumericOp
classifyOp A.Plus = NumericOp
classifyOp A.Minus = NumericOp
classifyOp A.Times = NumericOp
classifyOp A.BitAnd = IntegerOp
classifyOp A.BitOr = IntegerOp
classifyOp A.BitXor = IntegerOp
classifyOp A.LeftShift = ShiftOp
classifyOp A.RightShift = ShiftOp
classifyOp A.And = BooleanOp
classifyOp A.Or = BooleanOp
classifyOp A.Eq = ComparisonOp
classifyOp A.NotEq = ComparisonOp
classifyOp A.Less = ComparisonOp
classifyOp A.More = ComparisonOp
classifyOp A.LessEq = ComparisonOp
classifyOp A.MoreEq = ComparisonOp
classifyOp A.After = ComparisonOp
classifyOp A.Concat = ListOp

-- | Check a monadic operator.
checkMonadicOp :: A.MonadicOp -> A.Expression -> PassM ()
checkMonadicOp op e
    =  do t <- typeOfExpression e
          let m = findMeta e
          case classifyMOp op of
            NumericOp -> checkNumeric m t
            IntegerOp -> checkInteger m t
            BooleanOp -> checkType m A.Bool t

-- | Check a dyadic operator.
checkDyadicOp :: A.DyadicOp -> A.Expression -> A.Expression -> PassM ()
checkDyadicOp op l r
    =  do lt <- typeOfExpression l
          let lm = findMeta l
          rt <- typeOfExpression r
          let rm = findMeta r
          case classifyOp op of
            NumericOp ->
              checkNumeric lm lt >> checkNumeric rm rt >> checkType rm lt rt
            IntegerOp ->
              checkInteger lm lt >> checkInteger rm rt >> checkType rm lt rt
            ShiftOp ->
              checkNumeric lm lt >> checkType rm A.Int rt
            BooleanOp ->
              checkType lm A.Bool lt >> checkType rm A.Bool rt
            ComparisonOp ->
              checkScalar lm lt >> checkScalar rm rt >> checkType rm lt rt
            ListOp ->
              checkList lm lt >> checkList rm rt >> checkType rm lt rt

-- | Check a function call.
checkFunctionCall :: Meta -> A.Name -> [A.Expression] -> Bool -> PassM ()
checkFunctionCall m n es singleOnly
    =  do st <- specTypeOfName n
          case st of
            A.Function _ _ rs fs _ ->
               do when (singleOnly && length rs /= 1) $
                    diePC m $ formatCode "Function % used in an expression returns more than one value" n
                  when (length es /= length fs) $
                    diePC m $ formatCode ("Function % called with wrong number of arguments; found " ++ (show $ length es) ++ ", expected " ++ (show $ length fs)) n
                  sequence_ [do rt <- typeOfExpression e
                                checkType (findMeta e) et rt
                             | (e, A.Formal _ et _) <- zip es fs]
            _ -> diePC m $ formatCode ("% is not a function; it's a " ++ show st) n

-- | Check an intrinsic function call.
checkIntrinsicFunctionCall :: Meta -> String -> [A.Expression] -> Bool
                              -> PassM ()
checkIntrinsicFunctionCall m s es singleOnly
    = case lookup s intrinsicFunctions of
        Just (rs, tns) ->
           do when (singleOnly && length rs /= 1) $
                dieP m $ "Intrinsic function " ++ s ++ " used in an expression returns more than one value"
              when (length es /= length tns) $
                dieP m $ "Intrinsic function " ++ s ++ " called with wrong number of arguments; found " ++ (show $ length es) ++ ", expected " ++ (show $ length tns)
              sequence_ [do rt <- typeOfExpression e
                            checkType (findMeta e) et rt
                         | (e, (et, _)) <- zip es tns]
        Nothing -> dieP m $ s ++ " is not an intrinsic function"

-- | Check a mobile allocation.
checkAllocMobile :: Meta -> A.Type -> Maybe A.Expression -> PassM ()
checkAllocMobile m rawT me
    =  do t <- underlyingType m rawT
          case t of
            A.Mobile innerT ->
               do case innerT of
                    A.Array ds _ -> sequence_ $ map checkFullDimension ds
                    _ -> ok
                  case me of
                    Just e ->
                       do et <- typeOfExpression e
                          checkType (findMeta e) innerT et
                    Nothing -> ok
            _ -> diePC m $ formatCode "Expected mobile type in allocation; found %" t
  where
    checkFullDimension :: A.Dimension -> PassM ()
    checkFullDimension A.UnknownDimension
        = dieP m $ "Type in allocation contains unknown dimensions"
    checkFullDimension _ = ok

-- | Check that a variable is writable.
checkWritable :: A.Variable -> PassM ()
checkWritable v
    =  do am <- abbrevModeOfVariable v
          case am of
            A.ValAbbrev -> dieP (findMeta v) $ "Expected a writable variable"
            _ -> ok

--}}}

-- | Check the AST for type consistency.
-- This is actually a series of smaller passes that check particular types
-- inside the AST, but it doesn't really make sense to split it up.
checkTypes :: Data t => t -> PassM t
checkTypes t =
    checkSubscripts t >>=
    checkLiterals >>=
    checkVariables >>=
    checkExpressions >>=
    checkInputItems >>=
    checkOutputItems >>=
    checkReplicators >>=
    checkChoices

checkSubscripts :: Data t => t -> PassM t
checkSubscripts = checkDepthM doSubscript
  where
    doSubscript :: A.Subscript -> PassM ()
    doSubscript (A.Subscript m _ e) = checkExpressionInt m e
    doSubscript (A.SubscriptFromFor m e f)
        = checkExpressionInt m e >> checkExpressionInt m f
    doSubscript (A.SubscriptFrom m e) = checkExpressionInt m e
    doSubscript (A.SubscriptFor m e) = checkExpressionInt m e
    doSubscript _ = ok

checkLiterals :: Data t => t -> PassM t
checkLiterals = checkDepthM doExpression
  where
    doExpression :: A.Expression -> PassM ()
    doExpression (A.Literal m t lr) = doLiteralRepr t lr
    doExpression _ = ok

    doLiteralRepr :: A.Type -> A.LiteralRepr -> PassM ()
    doLiteralRepr t (A.ArrayLiteral m aes)
        = doArrayElem m t (A.ArrayElemArray aes)
    doLiteralRepr t (A.RecordLiteral m es)
        =  do rfs <- underlyingType m t >>= recordFields m
              when (length es /= length rfs) $
                dieP m $ "Record literal has wrong number of fields: found " ++ (show $ length es) ++ ", expected " ++ (show $ length rfs)
              sequence_ [checkExpressionType (findMeta fe) ft fe
                         | ((_, ft), fe) <- zip rfs es]
    doLiteralRepr _ _ = ok

    doArrayElem :: Meta -> A.Type -> A.ArrayElem -> PassM ()
    doArrayElem m t (A.ArrayElemArray aes)
        =  do checkArraySize m t (length aes)
              t' <- subscriptType (A.Subscript m A.NoCheck undefined) t
              sequence_ $ map (doArrayElem m t') aes
    doArrayElem _ t (A.ArrayElemExpr e) = checkExpressionType (findMeta e) t e

checkVariables :: Data t => t -> PassM t
checkVariables = checkDepthM doVariable
  where
    doVariable :: A.Variable -> PassM ()
    doVariable (A.SubscriptedVariable m s v)
        =  do t <- typeOfVariable v
              checkSubscriptType m s t
    doVariable (A.DirectedVariable m _ v)
        =  do t <- typeOfVariable v >>= underlyingType m
              case t of
                A.Chan _ _ _ -> ok
                _ -> dieP m $ "Direction applied to non-channel variable"
    doVariable (A.DerefVariable m v)
        =  do t <- typeOfVariable v >>= underlyingType m
              case t of
                A.Mobile _ -> ok
                _ -> dieP m $ "Dereference applied to non-mobile variable"
    doVariable _ = ok

checkExpressions :: Data t => t -> PassM t
checkExpressions = checkDepthM doExpression
  where
    doExpression :: A.Expression -> PassM ()
    doExpression (A.Monadic _ op e) = checkMonadicOp op e
    doExpression (A.Dyadic _ op le re) = checkDyadicOp op le re
    doExpression (A.MostPos m t) = checkNumeric m t
    doExpression (A.MostNeg m t) = checkNumeric m t
    doExpression (A.SizeType m t) = checkSequence m t
    doExpression (A.SizeExpr m e)
        =  do t <- typeOfExpression e
              checkSequence m t
    doExpression (A.SizeVariable m v)
        =  do t <- typeOfVariable v
              checkSequence m t
    doExpression (A.Conversion m _ t e)
        =  do et <- typeOfExpression e
              checkScalar m t >> checkScalar (findMeta e) et
    doExpression (A.FunctionCall m n es)
        = checkFunctionCall m n es True
    doExpression (A.IntrinsicFunctionCall m s es)
        = checkIntrinsicFunctionCall m s es True
    doExpression (A.SubscriptedExpr m s e)
        =  do t <- typeOfExpression e
              checkSubscriptType m s t
    doExpression (A.OffsetOf m rawT n)
        =  do t <- underlyingType m rawT
              checkRecordField m t n
    doExpression (A.AllocMobile m t me) = checkAllocMobile m t me
    doExpression _ = ok

checkInputItems :: Data t => t -> PassM t
checkInputItems = checkDepthM doInputItem
  where
    doInputItem :: A.InputItem -> PassM ()
    doInputItem (A.InCounted m cv av)
        =  do ct <- typeOfVariable cv
              checkInteger (findMeta cv) ct
              checkWritable cv
              at <- typeOfVariable av
              checkArray (findMeta av) at
              checkCommunicable (findMeta av) at
              checkWritable av
    doInputItem (A.InVariable _ v)
        =  do t <- typeOfVariable v
              checkCommunicable (findMeta v) t
              checkWritable v

checkOutputItems :: Data t => t -> PassM t
checkOutputItems = checkDepthM doOutputItem
  where
    doOutputItem :: A.OutputItem -> PassM ()
    doOutputItem (A.OutCounted m ce ae)
        =  do ct <- typeOfExpression ce
              checkInteger (findMeta ce) ct
              at <- typeOfExpression ae
              checkArray (findMeta ae) at
              checkCommunicable (findMeta ae) at
    doOutputItem (A.OutExpression _ e)
        =  do t <- typeOfExpression e
              checkCommunicable (findMeta e) t

checkReplicators :: Data t => t -> PassM t
checkReplicators = checkDepthM doReplicator
  where
    doReplicator :: A.Replicator -> PassM ()
    doReplicator (A.For _ _ start count)
        =  do checkExpressionInt (findMeta start) start
              checkExpressionInt (findMeta count) count
    doReplicator (A.ForEach _ _ e)
        =  do t <- typeOfExpression e
              checkSequence (findMeta e) t

checkChoices :: Data t => t -> PassM t
checkChoices = checkDepthM doChoice
  where
    doChoice :: A.Choice -> PassM ()
    doChoice (A.Choice _ e _) = checkExpressionBool (findMeta e) e

