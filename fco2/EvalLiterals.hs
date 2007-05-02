-- | Evaluate simple literal expressions.
module EvalLiterals where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
import Data.Bits
import Data.Char
import Data.Generics
import Data.Int
import Data.Maybe
import Numeric

import qualified AST as A
import Errors
import ParseState

type EvalM = ErrorT String (StateT ParseState Identity)

instance Die EvalM where
  die = throwError

-- | Occam values of various types.
data OccValue =
  OccBool Bool
  | OccByte Char
  | OccInt Int32
  | OccArray [OccValue]
  deriving (Show, Eq, Typeable, Data)

-- | Is an expression a constant literal?
isConstant :: A.Expression -> Bool
isConstant (A.Literal _ _ (A.ArrayLiteral _ aes))
    = and $ map isConstantArray aes
isConstant (A.Literal _ _ _) = True
isConstant (A.True _) = True
isConstant (A.False _) = True
isConstant _ = False

-- | Is an array literal element constant?
isConstantArray :: A.ArrayElem -> Bool
isConstantArray (A.ArrayElemArray aes) = and $ map isConstantArray aes
isConstantArray (A.ArrayElemExpr e) = isConstant e

-- | Evaluate a constant integer expression.
evalIntExpression :: (PSM m, Die m) => A.Expression -> m Int
evalIntExpression e
    =  do ps <- get
          case runEvaluator ps (evalSimpleExpression e) of
            Left err -> die $ "cannot evaluate expression: " ++ err
            Right (OccInt val) -> return $ fromIntegral val
            Right _ -> die "expression is not of INT type"

-- | Evaluate a byte literal.
evalByte :: (PSM m, Die m) => String -> m Char
evalByte s
    =  do ps <- get
          case runEvaluator ps (evalByteLiteral s) of
            Left err -> die $ "cannot evaluate byte literal: " ++ err
            Right (OccByte ch) -> return ch

-- | Run an evaluator operation.
runEvaluator :: ParseState -> EvalM OccValue -> Either String OccValue
runEvaluator ps func
    = runIdentity (evalStateT (runErrorT func) ps)

-- | Evaluate a simple literal expression.
evalSimpleExpression :: A.Expression -> EvalM OccValue
evalSimpleExpression e@(A.Literal _ _ _) = evalSimpleLiteral e
evalSimpleExpression _ = throwError "not a literal"

-- | Turn the result of one of the read* functions into an OccValue,
-- or throw an error if it didn't parse.
fromRead :: (t -> OccValue) -> (String -> [(t, String)]) -> String -> EvalM OccValue
fromRead cons reader s
    = case reader s of
        [(v, "")] -> return $ cons v
        _ -> throwError $ "cannot parse literal: " ++ s

-- | Evaluate a simple (non-array) literal.
evalSimpleLiteral :: A.Expression -> EvalM OccValue
evalSimpleLiteral (A.Literal _ A.Byte (A.ByteLiteral _ s)) = evalByteLiteral s
evalSimpleLiteral (A.Literal _ A.Int (A.IntLiteral _ s))
    = fromRead OccInt (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Int (A.HexLiteral _ s)) = fromRead OccInt readHex s
evalSimpleLiteral l = throwError $ "bad literal: " ++ show l

-- | Evaluate a byte literal.
evalByteLiteral :: String -> EvalM OccValue
evalByteLiteral ('*':'#':hex)
    = do OccInt n <- fromRead OccInt readHex hex
         return $ OccByte (chr $ fromIntegral n)
evalByteLiteral ['*', ch]
    = return $ OccByte (star ch)
  where
    star :: Char -> Char
    star 'c' = '\r'
    star 'n' = '\n'
    star 't' = '\t'
    star 's' = ' '
    star c = c
evalByteLiteral [ch]
    = return $ OccByte ch
evalByteLiteral _ = throwError "bad BYTE literal"
