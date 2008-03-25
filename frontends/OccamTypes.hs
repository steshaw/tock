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

-- | Check a subscript.
checkSubscript :: Meta -> A.Subscript -> A.Type -> PassM ()
checkSubscript m s rawT
    =  do -- Check the type of the thing being subscripted.
          t <- underlyingType m rawT
          case s of
            -- A record subscript.
            A.SubscriptField m n ->
              checkRecordField m t n
            -- A sequence subscript.
            A.Subscript _ _ _ -> checkSequence m t
            -- An array slice.
            _ -> checkArray m t

          -- Check the subscript itself.
          case s of
            A.Subscript m _ e -> checkExpressionInt m e
            A.SubscriptFromFor m e f ->
              checkExpressionInt m e >> checkExpressionInt m f
            A.SubscriptFrom m e -> checkExpressionInt m e
            A.SubscriptFor m e -> checkExpressionInt m e
            _ -> ok

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
checkFunctionCall :: Meta -> A.Name -> [A.Expression] -> PassM [A.Type]
checkFunctionCall m n es
    =  do st <- specTypeOfName n
          case st of
            A.Function _ _ rs fs _ ->
               do when (length es /= length fs) $
                    diePC m $ formatCode ("Function % called with wrong number of arguments; found " ++ (show $ length es) ++ ", expected " ++ (show $ length fs)) n
                  sequence_ [do rt <- typeOfExpression e
                                checkType (findMeta e) et rt
                             | (e, A.Formal _ et _) <- zip es fs]
                  return rs
            _ -> diePC m $ formatCode "% is not a function" n

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

-- | Check that is a variable is a channel that can be used in the given
-- direction.
-- If the direction passed is 'DirUnknown', no direction or sharedness checks
-- will be performed.
-- Return the type carried by the channel.
checkChannel :: A.Direction -> A.Variable -> PassM A.Type
checkChannel wantDir c
    =  do -- Check it's a channel.
          t <- typeOfVariable c >>= underlyingType m
          case t of
            A.Chan dir (A.ChanAttributes ws rs) innerT ->
               do -- Check the direction is appropriate 
                  case (wantDir, dir) of
                    (A.DirUnknown, _) -> ok
                    (_, A.DirUnknown) -> ok
                    (a, b) -> when (a /= b) $
                                dieP m $ "Channel directions do not match"

                  -- Check it's not shared in the direction we're using.
                  case (ws, rs, wantDir) of
                    (False, _, A.DirOutput) -> ok
                    (_, False, A.DirInput) -> ok
                    (_, _, A.DirUnknown) -> ok
                    _ -> dieP m $ "Shared channel must be claimed before use"

                  return innerT
            _ -> diePC m $ formatCode "Expected channel; found %" t
  where
    m = findMeta c

-- | Return the list of types carried by a protocol.
-- For a variant protocol, the second argument should be 'Just' the tag.
-- For a non-variant protocol, the second argument should be 'Nothing'.
protocolTypes :: Meta -> A.Type -> Maybe A.Name -> PassM [A.Type]
protocolTypes m t tag
    = case t of
        -- A user-defined protocol.
        A.UserProtocol n ->
           do st <- specTypeOfName n
              case (st, tag) of
                -- A simple protocol.
                (A.Protocol _ ts, Nothing) -> return ts
                (A.Protocol _ _, Just tagName) ->
                  diePC m $ formatCode "Tag % specified for non-variant protocol %" tagName n
                -- A variant protocol.
                (A.ProtocolCase _ ntss, Just tagName) ->
                  case lookup tagName ntss of
                    Just ts -> return ts
                    Nothing -> diePC m $ formatCode "Tag % not found in protocol %; expected one of %" tagName n (map fst ntss)
                (A.ProtocolCase _ _, Nothing) ->
                  diePC m $ formatCode "No tag specified for variant protocol %" n
                -- Not actually a protocol.
                _ -> diePC m $ formatCode "% is not a protocol" n
        -- Not a protocol (e.g. CHAN INT); just return it.
        _ -> return [t]

-- | Check a protocol communication.
-- Figure out the types of the items that should be involved in a protocol
-- communication, and run the supplied check against each item with its type.
checkProtocol :: Meta -> A.Type -> Maybe A.Name
                 -> [t] -> (A.Type -> t -> PassM ()) -> PassM ()
checkProtocol m t tag items doItem
    =  do its <- protocolTypes m t tag
          when (length its /= length items) $
            dieP m $ "Wrong number of items in protocol communication; found "
                     ++ (show $ length items) ++ ", expected "
                     ++ (show $ length its)
          sequence_ [doItem it item
                     | (it, item) <- zip its items]

checkExpressionList :: [A.Type] -> A.ExpressionList -> PassM ()
checkExpressionList ets el
    = case el of
        A.FunctionCallList m n es ->
           do rs <- checkFunctionCall m n es
              when (length ets /= length rs) $
                diePC m $ formatCode ("Function % has wrong number of return values; found " ++ (show $ length rs) ++ ", expected " ++ (show $ length ets)) n
              sequence_ [checkType m et rt
                         | (et, rt) <- zip ets rs]
        A.ExpressionList m es ->
           do when (length ets /= length es) $
                dieP m $ "Wrong number of items in expression list; found "
                         ++ (show $ length es) ++ ", expected "
                         ++ (show $ length ets)
              sequence_ [do rt <- typeOfExpression e
                            checkType (findMeta e) et rt
                         | (e, et) <- zip es ets]

--}}}

-- | Check the AST for type consistency.
-- This is actually a series of smaller passes that check particular types
-- inside the AST, but it doesn't really make sense to split it up.
checkTypes :: Data t => t -> PassM t
checkTypes t =
    checkSpecTypes t >>=
    checkVariables >>=
    checkExpressions >>=
    checkProcesses

--{{{  checkSpecTypes

checkSpecTypes :: Data t => t -> PassM t
checkSpecTypes = checkDepthM doSpecType
  where
    doSpecType :: A.SpecType -> PassM ()
    doSpecType _ = ok

--}}}
--{{{  checkVariables

checkVariables :: Data t => t -> PassM t
checkVariables = checkDepthM doVariable
  where
    doVariable :: A.Variable -> PassM ()
    doVariable (A.SubscriptedVariable m s v)
        =  do t <- typeOfVariable v
              checkSubscript m s t
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

--}}}
--{{{  checkExpressions

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
    doExpression (A.Literal m t lr) = doLiteralRepr t lr
    doExpression (A.FunctionCall m n es)
        =  do rs <- checkFunctionCall m n es
              when (length rs /= 1) $
                diePC m $ formatCode "Function % used in an expression returns more than one value" n
    doExpression (A.IntrinsicFunctionCall m s es)
        = checkIntrinsicFunctionCall m s es True
    doExpression (A.SubscriptedExpr m s e)
        =  do t <- typeOfExpression e
              checkSubscript m s t
    doExpression (A.OffsetOf m rawT n)
        =  do t <- underlyingType m rawT
              checkRecordField m t n
    doExpression (A.AllocMobile m t me) = checkAllocMobile m t me
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

--}}}
--{{{  checkProcesses

checkProcesses :: Data t => t -> PassM t
checkProcesses = checkDepthM doProcess
  where
    doProcess :: A.Process -> PassM ()
    doProcess (A.Assign m vs el)
        =  do vts <- mapM (typeOfVariable) vs
              mapM_ checkWritable vs
              checkExpressionList vts el
    doProcess (A.Input _ v im) = doInput v im
    doProcess (A.Output m v ois) = doOutput m v ois
    doProcess (A.OutputCase m v tag ois) = doOutputCase m v tag ois
    -- GetTime
    -- Wait
    -- ClearMobile
    -- Skip
    -- Stop
    doProcess (A.Seq _ s) = doStructured (\p -> ok) s
    doProcess (A.If _ s) = doStructured doChoice s
    -- Case
    -- While
    -- Par
    -- Processor
    -- Alt
    -- ProcCall
    -- IntrinsicProcCall
    doProcess _ = ok

    doChoice :: A.Choice -> PassM ()
    doChoice (A.Choice _ e _) = checkExpressionBool (findMeta e) e

    doInput :: A.Variable -> A.InputMode -> PassM ()
    doInput c (A.InputSimple m iis)
        =  do t <- checkChannel A.DirInput c
              checkProtocol m t Nothing iis doInputItem
    doInput c (A.InputCase _ s)
        =  do t <- checkChannel A.DirInput c
              doStructured (doVariant t) s
      where
        doVariant :: A.Type -> A.Variant -> PassM ()
        doVariant t (A.Variant m tag iis _)
            = checkProtocol m t (Just tag) iis doInputItem
    -- InputTimerRead
    -- InputTimerAfter
    doInput _ _ = ok

    doInputItem :: A.Type -> A.InputItem -> PassM ()
    doInputItem (A.Counted wantCT wantAT) (A.InCounted m cv av)
        =  do ct <- typeOfVariable cv
              checkType (findMeta cv) wantCT ct
              checkWritable cv
              at <- typeOfVariable av
              checkType (findMeta cv) wantAT at
              checkWritable av
    doInputItem t@(A.Counted _ _) (A.InVariable m v)
        = diePC m $ formatCode "Expected counted item of type %; found %" t v
    doInputItem wantT (A.InVariable _ v)
        =  do t <- typeOfVariable v
              checkType (findMeta v) wantT t
              checkWritable v

    doOutput :: Meta -> A.Variable -> [A.OutputItem] -> PassM ()
    doOutput m c ois
        =  do t <- checkChannel A.DirOutput c
              checkProtocol m t Nothing ois doOutputItem

    doOutputCase :: Meta -> A.Variable -> A.Name -> [A.OutputItem] -> PassM ()
    doOutputCase m c tag ois
        =  do t <- checkChannel A.DirOutput c
              checkProtocol m t (Just tag) ois doOutputItem

    doOutputItem :: A.Type -> A.OutputItem -> PassM ()
    doOutputItem (A.Counted wantCT wantAT) (A.OutCounted m ce ae)
        =  do ct <- typeOfExpression ce
              checkType (findMeta ce) wantCT ct
              at <- typeOfExpression ae
              checkType (findMeta ae) wantAT at
    doOutputItem t@(A.Counted _ _) (A.OutExpression m e)
        = diePC m $ formatCode "Expected counted item of type %; found %" t e
    doOutputItem wantT (A.OutExpression _ e)
        =  do t <- typeOfExpression e
              checkType (findMeta e) wantT t

    doReplicator :: A.Replicator -> PassM ()
    doReplicator (A.For _ _ start count)
        =  do checkExpressionInt (findMeta start) start
              checkExpressionInt (findMeta count) count
    doReplicator (A.ForEach _ _ e)
        =  do t <- typeOfExpression e
              checkSequence (findMeta e) t

    doStructured :: Data t => (t -> PassM ()) -> A.Structured t -> PassM ()
    doStructured doInner (A.Rep _ rep s)
        = doReplicator rep >> doStructured doInner s
    doStructured doInner (A.Spec _ spec s)
        = doStructured doInner s
    doStructured doInner (A.ProcThen _ p s)
        = doStructured doInner s
    doStructured doInner (A.Only _ i)
        = doInner i
    doStructured doInner (A.Several _ ss)
        = mapM_ (doStructured doInner) ss

--}}}

