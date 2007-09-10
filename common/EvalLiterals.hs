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
import Data.Word
import Numeric

import qualified AST as A
import CompState
import Errors

type EvalM = ErrorT String (StateT CompState Identity)

instance Die EvalM where
  die = throwError

-- | Occam values of various types.
data OccValue =
  OccBool Bool
  | OccByte Word8
  -- The following four aren't occam types, but I need to put them in here for handling Rain code:
  | OccUInt16 Word16
  | OccUInt32 Word32
  | OccUInt64 Word64
  | OccInt8 Int8
  
  | OccInt Int32
  | OccInt16 Int16
  | OccInt32 Int32
  | OccInt64 Int64
  -- FIXME This should include the type of the elements, so we can handle
  -- empty arrays.
  | OccArray [OccValue]
  | OccRecord A.Name [OccValue]
  deriving (Show, Eq, Typeable, Data)

-- | Is an expression a constant literal?
isConstant :: A.Expression -> Bool
isConstant (A.Literal _ _ (A.ArrayLiteral _ aes))
    = and $ map isConstantArray aes
isConstant (A.Literal _ _ (A.RecordLiteral _ es))
    = and $ map isConstant es
isConstant (A.Literal _ _ _) = True
isConstant (A.True _) = True
isConstant (A.False _) = True
isConstant _ = False

-- | Is an array literal element constant?
isConstantArray :: A.ArrayElem -> Bool
isConstantArray (A.ArrayElemArray aes) = and $ map isConstantArray aes
isConstantArray (A.ArrayElemExpr e) = isConstant e

-- | Evaluate a constant integer expression.
evalIntExpression :: (CSM m, Die m) => A.Expression -> m Int
evalIntExpression e
    =  do ps <- get
          case runEvaluator ps (evalSimpleExpression e) of
            Left err -> die $ "cannot evaluate expression: " ++ err
            Right (OccInt val) -> return $ fromIntegral val
            Right _ -> die "expression is not of INT type"

-- | Evaluate a byte literal.
evalByte :: (CSM m, Die m) => String -> m Char
evalByte s
    =  do ps <- get
          case runEvaluator ps (evalByteLiteral s) of
            Left err -> die $ "cannot evaluate byte literal: " ++ err
            Right (OccByte ch) -> return (chr $ fromIntegral ch)

-- | Run an evaluator operation.
runEvaluator :: CompState -> EvalM OccValue -> Either String OccValue
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
evalSimpleLiteral (A.Literal _ A.Byte (A.ByteLiteral _ s))
    = evalByteLiteral s
evalSimpleLiteral (A.Literal _ A.Byte (A.IntLiteral _ s))
    = fromRead OccByte (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Byte (A.HexLiteral _ s))
    = fromRead OccByte readHex s
evalSimpleLiteral (A.Literal _ A.UInt16 (A.IntLiteral _ s))
    = fromRead OccUInt16 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.UInt16 (A.HexLiteral _ s))
    = fromRead OccUInt16 readHex s
evalSimpleLiteral (A.Literal _ A.UInt32 (A.IntLiteral _ s))
    = fromRead OccUInt32 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.UInt32 (A.HexLiteral _ s))
    = fromRead OccUInt32 readHex s
evalSimpleLiteral (A.Literal _ A.UInt64 (A.IntLiteral _ s))
    = fromRead OccUInt64 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.UInt64 (A.HexLiteral _ s))
    = fromRead OccUInt64 readHex s
evalSimpleLiteral (A.Literal _ A.Int8 (A.IntLiteral _ s))
    = fromRead OccInt8 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Int8 (A.HexLiteral _ s))
    = fromRead OccInt8 readHex s
evalSimpleLiteral (A.Literal _ A.Int (A.IntLiteral _ s))
    = fromRead OccInt (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Int (A.HexLiteral _ s))
    = fromRead OccInt readHex s
evalSimpleLiteral (A.Literal _ A.Int16 (A.IntLiteral _ s))
    = fromRead OccInt16 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Int16 (A.HexLiteral _ s))
    = fromRead OccInt16 readHex s
evalSimpleLiteral (A.Literal _ A.Int32 (A.IntLiteral _ s))
    = fromRead OccInt32 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Int32 (A.HexLiteral _ s))
    = fromRead OccInt32 readHex s
evalSimpleLiteral (A.Literal _ A.Int64 (A.IntLiteral _ s))
    = fromRead OccInt64 (readSigned readDec) s
evalSimpleLiteral (A.Literal _ A.Int64 (A.HexLiteral _ s))
    = fromRead OccInt64 readHex s
evalSimpleLiteral l = throwError $ "bad literal: " ++ show l

-- | Evaluate a byte literal.
evalByteLiteral :: String -> EvalM OccValue
evalByteLiteral ('*':'#':hex)
    = do OccInt n <- fromRead OccInt readHex hex
         return $ OccByte (fromIntegral n)
evalByteLiteral ['*', ch]
    = return $ OccByte (fromIntegral $ ord $ star ch)
  where
    star :: Char -> Char
    star 'c' = '\r'
    star 'n' = '\n'
    star 't' = '\t'
    star 's' = ' '
    star c = c
evalByteLiteral [ch]
    = return $ OccByte (fromIntegral $ ord ch)
evalByteLiteral _ = throwError "bad BYTE literal"