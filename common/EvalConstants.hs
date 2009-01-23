{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

-- | Evaluate constant expressions.
module EvalConstants
    ( constantFold
    , evalIntExpression
    , isConstantName
    ) where

import Control.Monad.Error
import Control.Monad.State
import Data.Bits
import Data.Char
import Data.Int
import Data.Maybe
import Text.Printf

import qualified AST as A
import CompState hiding (CSM) -- everything here is read-only
import Errors
import EvalLiterals
import Metadata
import ShowCode
import Types
import Utils

-- | Simplify an expression by constant folding, and also return whether it's a
-- constant after that.
constantFold :: (CSMR m, Die m) => A.Expression -> m (A.Expression, Bool, ErrorReport)
constantFold e
    =  do ps <- getCompState
          t <- astTypeOf e
          case runEvaluator ps (evalExpression e) of
            Left err -> return (e, False, err)
            Right val ->
              do e' <- renderValue (findMeta e) t val
                 return (e', isConstant e', (Nothing, "already folded"))

-- | Evaluate a constant integer expression.
evalIntExpression :: (CSMR m, Die m) => A.Expression -> m Int
evalIntExpression e
    =  do ps <- getCompState
          case runEvaluator ps (evalExpression e) of
            Left (m, err) -> dieReport (m, "cannot evaluate expression: " ++ err)
            Right (OccInt val) -> return $ fromIntegral val
            Right _ -> dieP (findMeta e) "expression is not of INT type"

-- | Is a name defined as a constant expression? If so, return its folded
-- value.
getConstantName :: (CSMR m, Die m) => A.Name -> m (Maybe A.Expression)
getConstantName n
    =  do st <- specTypeOfName n
          case st of
            A.IsExpr _ A.ValAbbrev _ e ->
               do (e', isConst, _) <- constantFold e
                  -- FIXME: This should update the definition if it's constant
                  -- (to avoid folding multiple times), but that would require
                  -- CSM rather than CSMR.
                  if isConst
                    then return $ Just e'
                    else return Nothing
            _ -> return Nothing

-- | Is a name defined as a constant expression?
isConstantName :: (CSMR m, Die m) => A.Name -> m Bool
isConstantName n
    =  do me <- getConstantName n
          return $ case me of
                     Just _ -> True
                     Nothing -> False

--{{{  expression evaluator
evalLiteral :: A.Expression -> EvalM OccValue
evalLiteral (A.Literal m _ (A.ArrayLiteral _ []))
    = throwError (Just m, "empty array")
evalLiteral (A.Literal _ _ (A.ArrayLiteral _ aes))
    = liftM OccArray (mapM evalLiteralArray aes)
evalLiteral (A.Literal _ (A.Record n) (A.RecordLiteral _ es))
    = liftM (OccRecord n) (mapM evalExpression es)
evalLiteral l = evalSimpleLiteral l

evalLiteralArray :: A.ArrayElem -> EvalM OccValue
evalLiteralArray (A.ArrayElemArray aes) = liftM OccArray (mapM evalLiteralArray aes)
evalLiteralArray (A.ArrayElemExpr e) = evalExpression e

evalVariable :: A.Variable -> EvalM OccValue
evalVariable (A.Variable m n)
    =  do me <- getConstantName n
          case me of
            Just e -> evalExpression e
            Nothing -> throwError (Just m, "non-constant variable " ++ show n ++ " used")
evalVariable (A.SubscriptedVariable _ sub v) = evalVariable v >>= evalSubscript sub
evalVariable (A.DirectedVariable _ _ v) = evalVariable v

evalIndex :: A.Expression -> EvalM Int
evalIndex e
    =  do index <- evalExpression e
          case index of
            OccInt n -> return $ fromIntegral n
            _ -> throwError (Just $ findMeta e, "index has non-INT type")

-- TODO should we obey the no-checking here, or not?
-- If it's not in bounds, we can't constant fold it, so no-checking would preclude constant folding...
evalSubscript :: A.Subscript -> OccValue -> EvalM OccValue
evalSubscript (A.Subscript m _ e) (OccArray vs)
    =  do index <- evalIndex e
          if index >= 0 && index < length vs
            then return $ vs !! index
            else throwError (Just m, "subscript out of range")
evalSubscript s _ = throwError (Just $ findMeta s, "invalid subscript")

evalExpression :: A.Expression -> EvalM OccValue
evalExpression (A.Monadic _ op e)
    =  do v <- evalExpression e
          evalMonadic op v
evalExpression (A.Dyadic _ op e1 e2)
    =  do v1 <- evalExpression e1
          v2 <- evalExpression e2
          evalDyadic op v1 v2
evalExpression (A.MostPos _ A.Byte) = return $ OccByte maxBound
evalExpression (A.MostNeg _ A.Byte) = return $ OccByte minBound
evalExpression (A.MostPos _ A.UInt16) = return $ OccUInt16 maxBound
evalExpression (A.MostNeg _ A.UInt16) = return $ OccUInt16 minBound
evalExpression (A.MostPos _ A.UInt32) = return $ OccUInt32 maxBound
evalExpression (A.MostNeg _ A.UInt32) = return $ OccUInt32 minBound
evalExpression (A.MostPos _ A.UInt64) = return $ OccUInt64 maxBound
evalExpression (A.MostNeg _ A.UInt64) = return $ OccUInt64 minBound
evalExpression (A.MostPos _ A.Int8) = return $ OccInt8 maxBound
evalExpression (A.MostNeg _ A.Int8) = return $ OccInt8 minBound
evalExpression (A.MostPos _ A.Int) = return $ OccInt maxBound
evalExpression (A.MostNeg _ A.Int) = return $ OccInt minBound
evalExpression (A.MostPos _ A.Int16) = return $ OccInt16 maxBound
evalExpression (A.MostNeg _ A.Int16) = return $ OccInt16 minBound
evalExpression (A.MostPos _ A.Int32) = return $ OccInt32 maxBound
evalExpression (A.MostNeg _ A.Int32) = return $ OccInt32 minBound
evalExpression (A.MostPos _ A.Int64) = return $ OccInt64 maxBound
evalExpression (A.MostNeg _ A.Int64) = return $ OccInt64 minBound
evalExpression (A.SizeExpr m e)
    =  do t <- astTypeOf e >>= underlyingType m
          case t of
            A.Array (A.Dimension n:_) _ -> evalExpression n
            _ ->
              do v <- evalExpression e
                 case v of
                   OccArray vs -> return $ OccInt (fromIntegral $ length vs)
                   _ -> throwError (Just m, "size of non-constant expression " ++ show e ++ " used")
evalExpression (A.SizeVariable m v)
    =  do t <- astTypeOf v >>= underlyingType m
          case t of
            A.Array (A.Dimension n:_) _ -> evalExpression n
            _ -> throwError (Just m, "size of non-fixed-size variable " ++ show v ++ " used")
evalExpression e@(A.Literal _ _ _) = evalLiteral e
evalExpression (A.ExprVariable _ v) = evalVariable v
evalExpression (A.True _) = return $ OccBool True
evalExpression (A.False _) = return $ OccBool False
evalExpression (A.SubscriptedExpr _ sub e) = evalExpression e >>= evalSubscript sub
evalExpression (A.BytesInExpr m e)
    =  do b <- astTypeOf e >>= underlyingType m >>= bytesInType
          case b of
            BIJust n -> evalExpression n
            _ -> throwError (Just m, "BYTESIN non-constant-size expression " ++ show e ++ " used")
evalExpression (A.BytesInType m t)
    =  do b <- underlyingType m t >>= bytesInType
          case b of
            BIJust n -> evalExpression n
            _ -> throwErrorC (Just m, formatCode "BYTESIN non-constant-size type % used" t)
evalExpression e = throwError (Just $ findMeta e, "bad expression")

evalMonadicOp :: (forall t. (Num t, Integral t, Bits t) => t -> t) -> OccValue -> EvalM OccValue
evalMonadicOp f (OccByte a) = return $ OccByte (f a)
evalMonadicOp f (OccUInt16 a) = return $ OccUInt16 (f a)
evalMonadicOp f (OccUInt32 a) = return $ OccUInt32 (f a)
evalMonadicOp f (OccUInt64 a) = return $ OccUInt64 (f a)
evalMonadicOp f (OccInt8 a) = return $ OccInt8 (f a)
evalMonadicOp f (OccInt a) = return $ OccInt (f a)
evalMonadicOp f (OccInt16 a) = return $ OccInt16 (f a)
evalMonadicOp f (OccInt32 a) = return $ OccInt32 (f a)
evalMonadicOp f (OccInt64 a) = return $ OccInt64 (f a)
evalMonadicOp _ v = throwError (Nothing, "monadic operator not implemented for this type: " ++ show v)

evalMonadic :: A.MonadicOp -> OccValue -> EvalM OccValue
-- This, oddly, is probably the most important rule here: "-4" isn't a literal
-- in occam, it's an operator applied to a literal.
evalMonadic A.MonadicSubtr a = evalMonadicOp negate a
evalMonadic A.MonadicMinus a = evalMonadicOp negate a
evalMonadic A.MonadicBitNot a = evalMonadicOp complement a
evalMonadic A.MonadicNot (OccBool b) = return $ OccBool (not b)
evalMonadic op _ = throwError (Nothing, "bad monadic op: " ++ show op)

evalDyadicOp :: (forall t. (Num t, Integral t, Bounded t, Bits t) => t -> t -> t) -> OccValue -> OccValue -> EvalM OccValue
evalDyadicOp f (OccByte a) (OccByte b) = return $ OccByte (f a b)
evalDyadicOp f (OccUInt16 a) (OccUInt16 b) = return $ OccUInt16 (f a b)
evalDyadicOp f (OccUInt32 a) (OccUInt32 b) = return $ OccUInt32 (f a b)
evalDyadicOp f (OccUInt64 a) (OccUInt64 b) = return $ OccUInt64 (f a b)
evalDyadicOp f (OccInt8 a) (OccInt8 b) = return $ OccInt8 (f a b)
evalDyadicOp f (OccInt a) (OccInt b) = return $ OccInt (f a b)
evalDyadicOp f (OccInt16 a) (OccInt16 b) = return $ OccInt16 (f a b)
evalDyadicOp f (OccInt32 a) (OccInt32 b) = return $ OccInt32 (f a b)
evalDyadicOp f (OccInt64 a) (OccInt64 b) = return $ OccInt64 (f a b)
evalDyadicOp _ v0 v1 = throwError (Nothing, "dyadic operator not implemented for these types: " ++ show v0 ++ " and " ++ show v1)

evalCompareOp :: (forall t. (Eq t, Ord t) => t -> t -> Bool) -> OccValue -> OccValue -> EvalM OccValue
evalCompareOp f (OccByte a) (OccByte b) = return $ OccBool (f a b)
evalCompareOp f (OccUInt16 a) (OccUInt16 b) = return $ OccBool (f a b)
evalCompareOp f (OccUInt32 a) (OccUInt32 b) = return $ OccBool (f a b)
evalCompareOp f (OccUInt64 a) (OccUInt64 b) = return $ OccBool (f a b)
evalCompareOp f (OccInt8 a) (OccInt8 b) = return $ OccBool (f a b)
evalCompareOp f (OccInt a) (OccInt b) = return $ OccBool (f a b)
evalCompareOp f (OccInt16 a) (OccInt16 b) = return $ OccBool (f a b)
evalCompareOp f (OccInt32 a) (OccInt32 b) = return $ OccBool (f a b)
evalCompareOp f (OccInt64 a) (OccInt64 b) = return $ OccBool (f a b)
evalCompareOp _ v0 v1 = throwError (Nothing, "comparison operator not implemented for these types: " ++ show v0 ++ " and " ++ show v1)

-- The idea is: set the lower N bits to zero,
-- then rotate right by N.
logicalShiftR :: Bits a => a -> Int -> a
logicalShiftR val 0 = val
logicalShiftR val n = rotateR (foldl clearBit val [0 .. (n - 1)]) n

-- | Equivalent to 'div', but handles @minBound `div` (-1)@ correctly.
-- (GHC's doesn't, at least as of 6.8.1.)
safeDiv :: (Integral a, Bounded a) => a -> a -> a
safeDiv a (-1) | a == minBound = 0 -- Should be an overflow
safeDiv a b = div a b

-- | Equivalent to 'rem', but handles @minBound `rem` (-1)@ correctly.
-- (GHC's doesn't, at least as of 6.8.1.)
safeRem :: (Integral a, Bounded a) => a -> a -> a
safeRem a (-1) | a == minBound = 0 -- The correct answer
safeRem a b = rem a b

evalDyadic :: A.DyadicOp -> OccValue -> OccValue -> EvalM OccValue
-- FIXME These should check for overflow.
evalDyadic A.Add a b = evalDyadicOp (+) a b
evalDyadic A.Subtr a b = evalDyadicOp (-) a b
evalDyadic A.Mul a b = evalDyadicOp (*) a b
evalDyadic A.Div a b = evalDyadicOp safeDiv a b
evalDyadic A.Rem a b = evalDyadicOp safeRem a b
-- ... end FIXME
evalDyadic A.Plus a b = evalDyadicOp (+) a b
evalDyadic A.Minus a b = evalDyadicOp (-) a b
evalDyadic A.Times a b = evalDyadicOp (*) a b
evalDyadic A.BitAnd a b = evalDyadicOp (.&.) a b
evalDyadic A.BitOr a b = evalDyadicOp (.|.) a b
evalDyadic A.BitXor a b = evalDyadicOp xor a b
evalDyadic A.LeftShift a (OccInt b)
    = evalMonadicOp (\v -> shiftL v (fromIntegral b)) a
evalDyadic A.RightShift a (OccInt b)
-- occam shifts are logical (no sign-extending) but Haskell only has the signed
-- shift.  So we use a custom shift
    = evalMonadicOp (\v -> logicalShiftR v (fromIntegral b)) a
evalDyadic A.And (OccBool a) (OccBool b) = return $ OccBool (a && b)
evalDyadic A.Or (OccBool a) (OccBool b) = return $ OccBool (a || b)
evalDyadic A.Eq a b = evalCompareOp (==) a b
evalDyadic A.NotEq a b = evalCompareOp (/=) a b
evalDyadic A.Less a b = evalCompareOp (<) a b
evalDyadic A.More a b = evalCompareOp (>) a b
evalDyadic A.LessEq a b = evalCompareOp (<=) a b
evalDyadic A.MoreEq a b = evalCompareOp (>=) a b
evalDyadic A.After (OccInt a) (OccInt b) = return $ OccBool ((a - b) > 0)
evalDyadic op _ _ = throwError (Nothing, "bad dyadic op: " ++ show op)
--}}}

--{{{  rendering values
-- | Convert an 'OccValue' back into a (literal) 'Expression'.
renderValue :: (CSMR m, Die m) => Meta -> A.Type -> OccValue -> m A.Expression
renderValue m _ (OccBool True) = return $ A.True m
renderValue m _ (OccBool False) = return $ A.False m
renderValue m t v
    =  do (t', lr) <- renderLiteral m t v
          return $ A.Literal m t' lr

-- | Convert an 'OccValue' back into a 'LiteralRepr'.
renderLiteral :: forall m. (CSMR m, Die m) => Meta -> A.Type -> OccValue -> m (A.Type, A.LiteralRepr)
renderLiteral m t v
    = case v of
        OccByte c ->
          return (t, A.ByteLiteral m $ renderChar (chr $ fromIntegral c))
        OccUInt16 i -> renderInt i
        OccUInt32 i -> renderInt i
        OccUInt64 i -> renderInt i
        OccInt8 i -> renderInt i
        OccInt i -> renderInt i
        OccInt16 i -> renderInt i
        OccInt32 i -> renderInt i
        OccInt64 i -> renderInt i
        OccArray vs -> renderArray vs
        OccRecord _ vs -> renderRecord vs
  where
    renderChar :: Char -> String
    renderChar '\'' = "*'"
    renderChar '\"' = "*\""
    renderChar '*' = "**"
    renderChar '\r' = "*c"
    renderChar '\n' = "*n"
    renderChar '\t' = "*t"
    renderChar c
      | (o < 32 || o > 127) = printf "*#%02x" o
      | otherwise           = [c]
      where o = ord c

    renderInt :: Show s => s -> m (A.Type, A.LiteralRepr)
    renderInt i = return (t, A.IntLiteral m $ show i)

    renderArray :: [OccValue] -> m (A.Type, A.LiteralRepr)
    renderArray vs
        =  do (t', aes) <- renderArrayElems t vs
              return (t', A.ArrayLiteral m aes)

    -- We must make sure to apply array sizes if we've learned them while
    -- expanding the literal.
    renderArrayElems :: A.Type -> [OccValue] -> m (A.Type, [A.ArrayElem])
    renderArrayElems t vs
        =  do subT <- trivialSubscriptType m t
              (ts, aes) <- mapM (renderArrayElem subT) vs >>* unzip
              let dim = makeDimension m $ length aes
                  t' = case ts of
                         [] -> applyDimension dim t
                         _ -> addDimensions [dim] (head ts)
              return (t', aes)

    renderArrayElem :: A.Type -> OccValue -> m (A.Type, A.ArrayElem)
    renderArrayElem t (OccArray vs)
        =  do (t', aes) <- renderArrayElems t vs
              return (t', A.ArrayElemArray aes)
    renderArrayElem t v
        =  do e <- renderValue m t v
              t' <- astTypeOf e
              return (t', A.ArrayElemExpr e)

    renderRecord :: [OccValue] -> m (A.Type, A.LiteralRepr)
    renderRecord vs
        =  do ts <- case t of
                      A.Infer -> return [A.Infer | _ <- vs]
                      _ -> recordFields m t >>* map snd
              es <- sequence [renderValue m fieldT v | (fieldT, v) <- zip ts vs]
              return (t, A.RecordLiteral m es)
--}}}
