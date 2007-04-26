-- | Evaluate constant expressions.
module EvalConstants (constantFold) where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.Generics
import Data.Int
import Data.Maybe
import Numeric

import qualified AST as A
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

-- | Is an expression a constant literal?
isConstant :: A.Expression -> Bool
-- Array literals are only constant if all their components are.
isConstant (A.ExprLiteral _ (A.Literal _ _ (A.ArrayLiteral _ es)))
    = and $ map isConstant es
isConstant (A.ExprLiteral _ _) = True
isConstant (A.True _) = True
isConstant (A.False _) = True
isConstant _ = False

-- | Attempt to simplify an expression as far as possible by precomputing
-- constant bits.
simplifyExpression :: ParseState -> A.Expression -> Either String A.Expression
simplifyExpression ps e
    = case runIdentity (evalStateT (runErrorT (evalExpression e)) ps) of
        Left err -> Left err
        Right val -> Right $ renderValue (metaOfExpression e) val

--{{{  expression evaluator
type EvalM a = ErrorT String (StateT ParseState Identity) a

-- | Occam values of various types.
data OccValue =
  OccBool Bool
  | OccInt Int32
  deriving (Show, Eq, Typeable, Data)

-- | Turn the result of one of the read* functions into an OccValue,
-- or throw an error if it didn't parse.
fromRead :: (t -> OccValue) -> [(t, String)] -> EvalM OccValue
fromRead cons [(v, "")] = return $ cons v
fromRead _ _ = throwError "cannot parse literal"

evalLiteral :: A.Literal -> EvalM OccValue
evalLiteral (A.Literal _ A.Int (A.IntLiteral _ s)) = fromRead OccInt $ readDec s
evalLiteral (A.Literal _ A.Int (A.HexLiteral _ s)) = fromRead OccInt $ readHex s
evalLiteral _ = throwError "bad literal"

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
evalExpression (A.ExprLiteral _ l) = evalLiteral l
evalExpression (A.ExprVariable _ (A.Variable _ n))
    =  do ps <- get
          case lookup (A.nameName n) (psConstants ps) of
            Just e -> evalExpression e
            Nothing -> throwError $ "non-constant variable " ++ show n ++ " used"
evalExpression (A.True _) = return $ OccBool True
evalExpression (A.False _) = return $ OccBool False
evalExpression _ = throwError "bad expression"

evalMonadic :: A.MonadicOp -> OccValue -> EvalM OccValue
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

-- | Convert a value back into a literal.
renderValue :: Meta -> OccValue -> A.Expression
renderValue m (OccInt i) = A.ExprLiteral m (A.Literal m A.Int (A.IntLiteral m $ show i))
renderValue m (OccBool True) = A.True m
renderValue m (OccBool False) = A.False m
--}}}
