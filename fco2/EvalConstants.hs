-- | Evaluate constant expressions.
module EvalConstants (constantFold, isConstantName, evalIntExpression) where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.Generics
import Data.Int
import Data.Maybe
import Numeric

import qualified AST as A
import Errors
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

-- | Evaluate a constant integer expression.
evalIntExpression :: (PSM m, Die m) => A.Expression -> m Int
evalIntExpression e
    =  do ps <- get
          case runEvaluator ps e of
            Left err -> die $ "cannot evaluate expression: " ++ err
            Right (OccInt val) -> return $ int32ToInt val
            Right _ -> die "expression is not of INT type"

-- | Attempt to simplify an expression as far as possible by precomputing
-- constant bits.
simplifyExpression :: ParseState -> A.Expression -> Either String A.Expression
simplifyExpression ps e
    = case runEvaluator ps e of
        Left err -> Left err
        Right val -> Right $ snd $ renderValue (metaOfExpression e) val

-- | Run the expression evaluator.
runEvaluator :: ParseState -> A.Expression -> Either String OccValue
runEvaluator ps e
    = runIdentity (evalStateT (runErrorT (evalExpression e)) ps)

--{{{  expression evaluator
type EvalM = ErrorT String (StateT ParseState Identity)

instance Die EvalM where
  die = throwError

-- | Occam values of various types.
data OccValue =
  OccBool Bool
  | OccInt Int32
  | OccArray [OccValue]
  deriving (Show, Eq, Typeable, Data)

-- | Turn the result of one of the read* functions into an OccValue,
-- or throw an error if it didn't parse.
fromRead :: (t -> OccValue) -> [(t, String)] -> EvalM OccValue
fromRead cons [(v, "")] = return $ cons v
fromRead _ _ = throwError "cannot parse literal"

evalLiteral :: A.Literal -> EvalM OccValue
evalLiteral (A.Literal _ A.Int (A.IntLiteral _ s)) = fromRead OccInt $ readDec s
evalLiteral (A.Literal _ A.Int (A.HexLiteral _ s)) = fromRead OccInt $ readHex s
evalLiteral (A.Literal _ _ (A.ArrayLiteral _ es))
    = liftM OccArray (mapM evalExpression es)
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
    =  do me <- getConstantName n
          case me of
            Just e -> evalExpression e
            Nothing -> throwError $ "non-constant variable " ++ show n ++ " used"
evalExpression (A.True _) = return $ OccBool True
evalExpression (A.False _) = return $ OccBool False
evalExpression _ = throwError "bad expression"

evalMonadic :: A.MonadicOp -> OccValue -> EvalM OccValue
-- This, oddly, is probably the most important rule here: "-4" isn't a literal
-- in occam, it's an operator applied to a literal.
evalMonadic A.MonadicSubtr (OccInt i) = return $ OccInt (0 - i)
evalMonadic A.MonadicBitNot (OccInt i) = return $ OccInt (complement i)
evalMonadic A.MonadicNot (OccBool b) = return $ OccBool (not b)
evalMonadic _ _ = throwError "bad monadic op"

int32ToInt :: Int32 -> Int
int32ToInt n = fromInteger (toInteger n)

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
evalDyadic A.LeftShift (OccInt a) (OccInt b) = return $ OccInt (shiftL a (int32ToInt b))
evalDyadic A.RightShift (OccInt a) (OccInt b) = return $ OccInt (shiftR a (int32ToInt b))
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
renderValue :: Meta -> OccValue -> (A.Type, A.Expression)
renderValue m (OccBool True) = (A.Bool, A.True m)
renderValue m (OccBool False) = (A.Bool, A.False m)
renderValue m v = (t, A.ExprLiteral m (A.Literal m t lr))
  where (t, lr) = renderLiteral m v

renderLiteral :: Meta -> OccValue -> (A.Type, A.LiteralRepr)
renderLiteral m (OccInt i) = (A.Int, A.IntLiteral m $ show i)
renderLiteral m (OccArray vs)
    = (t, A.ArrayLiteral m es)
  where
    t = makeArrayType (A.Dimension $ length vs) (head ts)
    (ts, es) = unzip $ map (renderValue m) vs
--}}}
