-- | Evaluate constant expressions.
module EvalConstants (constantFold, isConstantName) where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.Char
import Data.Generics
import Data.Int
import Data.Maybe
import Data.Word
import Numeric
import Text.Printf

import qualified AST as A
import Errors
import EvalLiterals
import Metadata
import ParseState
import Pass
import Types

-- | Simplify an expression by constant folding, and also return whether it's a
-- constant after that.
constantFold :: PSM m => A.Expression -> m (A.Expression, Bool, String)
constantFold e
    =  do ps <- get
          let (e', msg) = case simplifyExpression ps e of
                            Left err -> (e, err)
                            Right val -> (val, "already folded")
          return (e', isConstant e', msg)

-- | Is a name defined as a constant expression? If so, return its definition.
getConstantName :: (PSM m, Die m) => A.Name -> m (Maybe A.Expression)
getConstantName n
    =  do st <- specTypeOfName n
          case st of
            A.IsExpr _ A.ValAbbrev _ e ->
              if isConstant e then return $ Just e
                              else return Nothing
            _ -> return Nothing

-- | Is a name defined as a constant expression?
isConstantName :: (PSM m, Die m) => A.Name -> m Bool
isConstantName n
    =  do me <- getConstantName n
          return $ case me of
                     Just _ -> True
                     Nothing -> False

-- | Attempt to simplify an expression as far as possible by precomputing
-- constant bits.
simplifyExpression :: ParseState -> A.Expression -> Either String A.Expression
simplifyExpression ps e
    = case runEvaluator ps (evalExpression e) of
        Left err -> Left err
        Right val -> Right $ snd $ renderValue (findMeta e) val

--{{{  expression evaluator
evalLiteral :: A.Expression -> EvalM OccValue
evalLiteral (A.Literal _ _ (A.ArrayLiteral _ []))
    = throwError "empty array"
evalLiteral (A.Literal _ _ (A.ArrayLiteral _ aes))
    = liftM OccArray (mapM evalLiteralArray aes)
evalLiteral l = evalSimpleLiteral l

evalLiteralArray :: A.ArrayElem -> EvalM OccValue
evalLiteralArray (A.ArrayElemArray aes) = liftM OccArray (mapM evalLiteralArray aes)
evalLiteralArray (A.ArrayElemExpr e) = evalExpression e

evalVariable :: A.Variable -> EvalM OccValue
evalVariable (A.Variable _ n)
    =  do me <- getConstantName n
          case me of
            Just e -> evalExpression e
            Nothing -> throwError $ "non-constant variable " ++ show n ++ " used"
evalVariable (A.SubscriptedVariable _ sub v) = evalVariable v >>= evalSubscript sub

evalIndex :: A.Expression -> EvalM Int
evalIndex e
    =  do index <- evalExpression e
          case index of
            OccInt n -> return $ fromIntegral n
            _ -> throwError $ "index has non-INT type"

evalSubscript :: A.Subscript -> OccValue -> EvalM OccValue
evalSubscript (A.Subscript _ e) (OccArray vs)
    =  do index <- evalIndex e
          if index >= 0 && index < length vs
            then return $ vs !! index
            else throwError $ "subscript out of range"
evalSubscript _ _ = throwError $ "invalid subscript"

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
evalExpression (A.MostPos _ A.Int) = return $ OccInt maxBound
evalExpression (A.MostNeg _ A.Int) = return $ OccInt minBound
evalExpression (A.MostPos _ A.Int16) = return $ OccInt16 maxBound
evalExpression (A.MostNeg _ A.Int16) = return $ OccInt16 minBound
evalExpression (A.MostPos _ A.Int32) = return $ OccInt32 maxBound
evalExpression (A.MostNeg _ A.Int32) = return $ OccInt32 minBound
evalExpression (A.MostPos _ A.Int64) = return $ OccInt64 maxBound
evalExpression (A.MostNeg _ A.Int64) = return $ OccInt64 minBound
evalExpression (A.SizeExpr _ e)
    =  do t <- typeOfExpression e
          case t of
            A.Array (A.Dimension n:_) _ -> return $ OccInt (fromIntegral n)
            _ ->
              do v <- evalExpression e
                 case v of
                   OccArray vs -> return $ OccInt (fromIntegral $ length vs)
                   _ -> throwError $ "size of non-constant expression " ++ show e ++ " used"
evalExpression (A.SizeVariable m v)
    =  do t <- typeOfVariable v
          case t of
            A.Array (A.Dimension n:_) _ -> return $ OccInt (fromIntegral n)
            _ -> throwError $ "size of non-fixed-size variable " ++ show v ++ " used"
evalExpression e@(A.Literal _ _ _) = evalLiteral e
evalExpression (A.ExprVariable _ v) = evalVariable v
evalExpression (A.True _) = return $ OccBool True
evalExpression (A.False _) = return $ OccBool False
evalExpression (A.SubscriptedExpr _ sub e) = evalExpression e >>= evalSubscript sub
evalExpression (A.BytesInExpr _ e)
    =  do t <- typeOfExpression e
          b <- bytesInType t
          case b of
            BIJust n -> return $ OccInt (fromIntegral $ n)
            _ -> throwError $ "BYTESIN non-constant-size expression " ++ show e ++ " used"
evalExpression (A.BytesInType _ t)
    =  do b <- bytesInType t
          case b of
            BIJust n -> return $ OccInt (fromIntegral $ n)
            _ -> throwError $ "BYTESIN non-constant-size type " ++ show t ++ " used"
evalExpression e = throwError "bad expression"

evalMonadicOp :: (forall t. (Num t, Integral t, Bits t) => t -> t) -> OccValue -> EvalM OccValue
evalMonadicOp f (OccByte a) = return $ OccByte (f a)
evalMonadicOp f (OccInt a) = return $ OccInt (f a)
evalMonadicOp f (OccInt16 a) = return $ OccInt16 (f a)
evalMonadicOp f (OccInt32 a) = return $ OccInt32 (f a)
evalMonadicOp f (OccInt64 a) = return $ OccInt64 (f a)
evalMonadicOp _ _ = throwError "monadic operator not implemented for this type"

evalMonadic :: A.MonadicOp -> OccValue -> EvalM OccValue
-- This, oddly, is probably the most important rule here: "-4" isn't a literal
-- in occam, it's an operator applied to a literal.
evalMonadic A.MonadicSubtr a = evalMonadicOp negate a
evalMonadic A.MonadicBitNot a = evalMonadicOp complement a
evalMonadic A.MonadicNot (OccBool b) = return $ OccBool (not b)
evalMonadic _ _ = throwError "bad monadic op"

evalDyadicOp :: (forall t. (Num t, Integral t, Bits t) => t -> t -> t) -> OccValue -> OccValue -> EvalM OccValue
evalDyadicOp f (OccByte a) (OccByte b) = return $ OccByte (f a b)
evalDyadicOp f (OccInt a) (OccInt b) = return $ OccInt (f a b)
evalDyadicOp f (OccInt16 a) (OccInt16 b) = return $ OccInt16 (f a b)
evalDyadicOp f (OccInt32 a) (OccInt32 b) = return $ OccInt32 (f a b)
evalDyadicOp f (OccInt64 a) (OccInt64 b) = return $ OccInt64 (f a b)
evalDyadicOp _ _ _ = throwError "dyadic operator not implemented for this type"

evalCompareOp :: (forall t. (Eq t, Ord t) => t -> t -> Bool) -> OccValue -> OccValue -> EvalM OccValue
evalCompareOp f (OccByte a) (OccByte b) = return $ OccBool (f a b)
evalCompareOp f (OccInt a) (OccInt b) = return $ OccBool (f a b)
evalCompareOp f (OccInt16 a) (OccInt16 b) = return $ OccBool (f a b)
evalCompareOp f (OccInt32 a) (OccInt32 b) = return $ OccBool (f a b)
evalCompareOp f (OccInt64 a) (OccInt64 b) = return $ OccBool (f a b)
evalCompareOp _ _ _ = throwError "comparison operator not implemented for this type"

evalDyadic :: A.DyadicOp -> OccValue -> OccValue -> EvalM OccValue
-- FIXME These should check for overflow.
evalDyadic A.Add a b = evalDyadicOp (+) a b
evalDyadic A.Subtr a b = evalDyadicOp (-) a b
evalDyadic A.Mul a b = evalDyadicOp (*) a b
evalDyadic A.Div a b = evalDyadicOp div a b
evalDyadic A.Rem a b = evalDyadicOp rem a b
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
    = evalMonadicOp (\v -> shiftR v (fromIntegral b)) a
evalDyadic A.And (OccBool a) (OccBool b) = return $ OccBool (a && b)
evalDyadic A.Or (OccBool a) (OccBool b) = return $ OccBool (a || b)
evalDyadic A.Eq a b = evalCompareOp (==) a b
evalDyadic A.NotEq a b = evalCompareOp (/=) a b
evalDyadic A.Less a b = evalCompareOp (<) a b
evalDyadic A.More a b = evalCompareOp (>) a b
evalDyadic A.LessEq a b = evalCompareOp (<=) a b
evalDyadic A.MoreEq a b = evalCompareOp (>=) a b
evalDyadic A.After (OccInt a) (OccInt b) = return $ OccBool ((a - b) > 0)
evalDyadic _ _ _ = throwError "bad dyadic op"
--}}}

--{{{  rendering values
-- | Convert a value back into a literal.
renderValue :: Meta -> OccValue -> (A.Type, A.Expression)
renderValue m (OccBool True) = (A.Bool, A.True m)
renderValue m (OccBool False) = (A.Bool, A.False m)
renderValue m v = (t, A.Literal m t lr)
  where (t, lr) = renderLiteral m v

renderLiteral :: Meta -> OccValue -> (A.Type, A.LiteralRepr)
renderLiteral m (OccByte c) = (A.Byte, A.ByteLiteral m $ renderChar (chr $ fromIntegral c))
renderLiteral m (OccInt i) = (A.Int, A.IntLiteral m $ show i)
renderLiteral m (OccInt16 i) = (A.Int16, A.IntLiteral m $ show i)
renderLiteral m (OccInt32 i) = (A.Int32, A.IntLiteral m $ show i)
renderLiteral m (OccInt64 i) = (A.Int64, A.IntLiteral m $ show i)
renderLiteral m (OccArray vs)
    = (t, A.ArrayLiteral m aes)
  where
    t = makeArrayType (A.Dimension $ length vs) (head ts)
    (ts, aes) = unzip $ map (renderLiteralArray m) vs

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

renderLiteralArray :: Meta -> OccValue -> (A.Type, A.ArrayElem)
renderLiteralArray m (OccArray vs)
    = (t, A.ArrayElemArray aes)
  where
    t = makeArrayType (A.Dimension $ length vs) (head ts)
    (ts, aes) = unzip $ map (renderLiteralArray m) vs
renderLiteralArray m v
    = (t, A.ArrayElemExpr e)
  where
    (t, e) = renderValue m v
--}}}
