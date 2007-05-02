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
evalExpression (A.MostPos _ A.Int) = return $ OccInt maxBound
evalExpression (A.MostNeg _ A.Int) = return $ OccInt minBound
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
evalExpression _ = throwError "bad expression"

evalMonadic :: A.MonadicOp -> OccValue -> EvalM OccValue
-- This, oddly, is probably the most important rule here: "-4" isn't a literal
-- in occam, it's an operator applied to a literal.
evalMonadic A.MonadicSubtr (OccInt i) = return $ OccInt (0 - i)
evalMonadic A.MonadicBitNot (OccInt i) = return $ OccInt (complement i)
evalMonadic A.MonadicNot (OccBool b) = return $ OccBool (not b)
evalMonadic _ _ = throwError "bad monadic op"

evalDyadic :: A.DyadicOp -> OccValue -> OccValue -> EvalM OccValue
-- FIXME These should check for overflow.
evalDyadic A.Add (OccInt a) (OccInt b) = return $ OccInt (a + b)
evalDyadic A.Subtr (OccInt a) (OccInt b) = return $ OccInt (a - b)
evalDyadic A.Mul (OccInt a) (OccInt b) = return $ OccInt (a * b)
evalDyadic A.Div (OccInt a) (OccInt b) = return $ OccInt (a `div` b)
evalDyadic A.Rem (OccInt a) (OccInt b) = return $ OccInt (a `mod` b)
-- ... end FIXME
evalDyadic A.Plus (OccInt a) (OccInt b) = return $ OccInt (a + b)
evalDyadic A.Minus (OccInt a) (OccInt b) = return $ OccInt (a - b)
evalDyadic A.Times (OccInt a) (OccInt b) = return $ OccInt (a * b)
evalDyadic A.BitAnd (OccInt a) (OccInt b) = return $ OccInt (a .&. b)
evalDyadic A.BitOr (OccInt a) (OccInt b) = return $ OccInt (a .|. b)
evalDyadic A.BitXor (OccInt a) (OccInt b) = return $ OccInt (a `xor` b)
evalDyadic A.LeftShift (OccInt a) (OccInt b) = return $ OccInt (shiftL a (fromIntegral b))
evalDyadic A.RightShift (OccInt a) (OccInt b) = return $ OccInt (shiftR a (fromIntegral b))
evalDyadic A.And (OccBool a) (OccBool b) = return $ OccBool (a && b)
evalDyadic A.Or (OccBool a) (OccBool b) = return $ OccBool (a || b)
evalDyadic A.Eq a b = return $ OccBool (a == b)
evalDyadic A.NotEq a b
    =  do (OccBool b) <- evalDyadic A.Eq a b
          return $ OccBool (not b)
evalDyadic A.Less (OccInt a) (OccInt b) = return $ OccBool (a < b)
evalDyadic A.More (OccInt a) (OccInt b) = return $ OccBool (a > b)
evalDyadic A.LessEq a b = evalDyadic A.More b a
evalDyadic A.MoreEq a b = evalDyadic A.Less b a
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
renderLiteral m (OccByte c) = (A.Byte, A.ByteLiteral m $ renderChar c)
renderLiteral m (OccInt i) = (A.Int, A.IntLiteral m $ show i)
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
