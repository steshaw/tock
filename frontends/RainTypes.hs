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

module RainTypes where

import qualified AST as A
import Pass
import Data.Generics
import EvalConstants
import Errors
import Types
import Control.Monad.State
import CompState
import Metadata


-- | A pass that records inferred types.  Currently the only place where types are inferred is in seqeach\/pareach loops.
recordInfNameTypes :: Data t => t -> PassM t
recordInfNameTypes = everywhereM (mkM recordInfNameTypes')
  where
    recordInfNameTypes' :: A.Replicator -> PassM A.Replicator
    recordInfNameTypes' input@(A.ForEach m n e)
      = do arrType <- typeOfExpression e
           innerT <- case arrType of 
             A.Array (_:innerDims) t ->
               return $ case innerDims of 
                 [] -> t
                 _ -> A.Array innerDims t               
             _ -> dieP m "Cannot do a foreach loop over a non-array type (or array with zero dimensions)"
           defineName n A.NameDef {A.ndMeta = m, A.ndName = A.nameName n, A.ndOrigName = A.nameName n, 
                                   A.ndNameType = A.VariableName, A.ndType = (A.Declaration m innerT), 
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return input
    recordInfNameTypes' r = return r

everywhereASTM :: (Data s, Data t) => (s -> PassM s) -> t -> PassM t
everywhereASTM f = doGeneric `extM` (doSpecific f)
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric (everywhereASTM f)
    
    doSpecific :: Data t => (t -> PassM t) -> t -> PassM t
    doSpecific f x = (doGeneric x >>= f)

-- | Folds all constants.
constantFoldPass :: Data t => t -> PassM t
constantFoldPass = everywhereASTM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression = (liftM (\(x,_,_) -> x)) . constantFold

-- | Annotates all integer literal types
annnotateIntLiteralTypes :: Data t => t -> PassM t
annnotateIntLiteralTypes = everywhereASTM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.Literal m t (A.IntLiteral m' s))
      = do t' <-       
             if (t == A.Int64) then --it's a signed literal
              (if (n >= 2^63 || n < (-(2^63))) 
                 then dieP m $ "Signed integer literal too large to fit into 64 bits: " ++ s
                 else 
                   if (n < (-(2^31)) || n >= 2^31)
                     then return A.Int64
                     else 
                       if (n < (-(2^15)) || n >= 2^15)
                         then return A.Int32
                         else
                           if (n < (-(2^7)) || n >= 2^7)
                             then return A.Int16
                             else return A.Int8
              )
              else
                dieP m $ "Unsigned literals currently unsupported"
           return $ A.Literal m t' (A.IntLiteral m' s)
      where
        n = read s        
    doExpression e = return e

-- | A pass that finds all the 'A.ProcCall' and 'A.FunctionCall' in the AST, and checks that the actual parameters are valid inputs, given the 'A.Formal' parameters in the process's type
matchParamPass :: Data t => t -> PassM t
matchParamPass = everywhereM ((mkM matchParamPassProc) `extM` matchParamPassFunc)
  where
    --Picks out the parameters of a process call, checks the number is correct, and maps doParam over them
    matchParamPassProc :: A.Process -> PassM A.Process
    matchParamPassProc (A.ProcCall m n actualParams)
      = do def <- lookupNameOrError n $ dieP m ("Process name is unknown: \"" ++ (show $ A.nameName n) ++ "\"")
           case A.ndType def of
             A.Proc _ _ expectedParams _ ->
               if (length expectedParams) == (length actualParams)
               then do transActualParams <- mapM (doParam m (A.nameName n)) (zip3 [0..] expectedParams actualParams)
                       return $ A.ProcCall m n transActualParams
               else dieP m $ "Wrong number of parameters given to process call; expected: " ++ show (length expectedParams) ++ " but found: " ++ show (length actualParams)
             _ -> dieP m $ "You cannot run things that are not processes, such as: \"" ++ (show $ A.nameName n) ++ "\""
    matchParamPassProc p = return p
    
    --Picks out the parameters of a function call, checks the number is correct, and maps doExpParam over them
    matchParamPassFunc :: A.Expression -> PassM A.Expression
    matchParamPassFunc (A.FunctionCall m n actualParams)
      = do def <- lookupNameOrError n $ dieP m ("Function name is unknown: \"" ++ (show $ A.nameName n) ++ "\"")
           case A.ndType def of
             A.Function _ _ _ expectedParams _ ->
               if (length expectedParams) == (length actualParams)
               then do transActualParams <- mapM (doExpParam m (A.nameName n)) (zip3 [0..] expectedParams actualParams)
                       return $ A.FunctionCall m n transActualParams
               else dieP m $ "Wrong number of parameters given to function call; expected: " ++ show (length expectedParams) ++ " but found: " ++ show (length actualParams)
             _ -> dieP m $ "Attempt to make a function call with something that is not a function: \"" ++ (show $ A.nameName n) ++ "\""
    matchParamPassFunc e = return e

    --Checks the type of a parameter (A.Actual), and inserts a cast if it is safe to do so
    doParam :: Meta -> String -> (Int,A.Formal, A.Actual) -> PassM A.Actual
    doParam m n (index, A.Formal formalAbbrev formalType formalName, A.ActualVariable _ _ v)
      = do actualType <- typeOfVariable v
           if (actualType == formalType)
             then return $ A.ActualVariable formalAbbrev formalType v
             else (liftM $ A.ActualExpression formalType) $ doCast index formalType actualType (A.ExprVariable (findMeta v) v )
    doParam m n (index, for@(A.Formal _ formalType _), A.ActualExpression _ e)
      = (liftM $ A.ActualExpression formalType) $ doExpParam m n (index, for, e)

    --Checks the type of a parameter (A.Expression), and inserts a cast if it is safe to do so
    doExpParam :: Meta -> String -> (Int, A.Formal, A.Expression) -> PassM A.Expression
    doExpParam m n (index, A.Formal formalAbbrev formalType formalName, e)
      = do actualType <- typeOfExpression e
           if (actualType == formalType)
             then return e
             else doCast index formalType actualType e

    doCast :: Int -> A.Type -> A.Type -> A.Expression -> PassM A.Expression
    doCast index = coerceType $ " for parameter (zero-based): " ++ (show index)

--Adds a cast between two types if it is safe to do so, otherwise gives an error
coerceType :: String -> A.Type -> A.Type -> A.Expression -> PassM A.Expression
coerceType customMsg to from item
      = if isImplicitConversionRain from to
          then return $ A.Conversion (findMeta item) A.DefaultConversion to item
          else dieP (findMeta item) $ "Could not perform implicit cast from supplied type: " ++ (show from) ++
            " to expected type: " ++ (show to) ++ customMsg


-- | Checks the types in expressions
checkExpressionTypes :: Data t => t -> PassM t
checkExpressionTypes = everywhereASTM checkExpression
  where
    checkExpression :: A.Expression -> PassM A.Expression
    checkExpression e@(A.Dyadic m op lhs rhs)
      = do tlhs <- typeOfExpression lhs
           trhs <- typeOfExpression rhs
           if (tlhs == trhs)
             then (if validOp op tlhs then return e else dieP m $ "Operator: \"" ++ show op ++ "\" is not valid on type: \"" ++ show tlhs)
             else if (isIntegerType tlhs && isIntegerType trhs) 
                    then case (leastGeneralSharedTypeRain [tlhs,trhs]) of
                           Nothing -> dieP m $ "Cannot find a suitable type to convert expression to, types are: " ++ show tlhs ++ " and " ++ show trhs
                           Just t -> if validOp op t then return $ A.Dyadic m op (convert t tlhs lhs) (convert t trhs rhs) else dieP m $
                             "Operator: \"" ++ show op ++ "\" is not valid on type: \"" ++ show tlhs
                    else --The operators are not equal, and are not integers.  Therefore this must be an error:
                      dieP m $ "Mis-matched types; no operator applies to types: " ++ show tlhs ++ " and " ++ show trhs
    checkExpression e@(A.Monadic m op rhs)
      = do trhs <- typeOfExpression rhs
           if (op == A.MonadicMinus)
             then case trhs of
                    A.Byte -> return $ A.Monadic m op $ convert A.Int16 trhs rhs
                    A.UInt16 -> return $ A.Monadic m op $ convert A.Int32 trhs rhs
                    A.UInt32 -> return $ A.Monadic m op $ convert A.Int64 trhs rhs
                    A.UInt64 -> dieP m $ "Cannot apply unary minus to type: " ++ show trhs ++ " because there is no type large enough to safely contain the result"
                    _ -> if (isIntegerType trhs) then return e else dieP m $ "Trying to apply unary minus to non-integer type: " ++ show trhs
             else if (op == A.MonadicNot)
                    then
                      case trhs of
                        A.Bool -> return e
                        _ -> dieP m $ "Cannot apply unary not to non-boolean type: " ++ show trhs
                    else dieP m $ "Invalid Rain operator: \"" ++ show op ++ "\""
    checkExpression e@(A.Conversion m cm dest rhs)
      = do src <- typeOfExpression rhs
           if (src == dest)
             then return e
             else if isImplicitConversionRain src dest
                    then return e
                    else dieP m $ "Invalid cast from: " ++ show dest ++ " to: " ++ show src
    checkExpression e = return e

    convert :: A.Type -> A.Type -> A.Expression -> A.Expression
    convert dest src e = if (dest == src)
                           then e
                           else A.Conversion (findMeta e) A.DefaultConversion dest e

    validOp :: A.DyadicOp -> A.Type -> Bool
    validOp A.Plus t = isIntegerType t
    validOp A.Minus t = isIntegerType t
    validOp A.Times t = isIntegerType t
    validOp A.Div t = isIntegerType t
    validOp A.Rem t = isIntegerType t
    validOp A.Eq _ = True
    validOp A.NotEq _ = True
    validOp A.Less t = haveOrder t
    validOp A.LessEq t = haveOrder t
    validOp A.More t = haveOrder t
    validOp A.MoreEq t = haveOrder t
    validOp A.And A.Bool = True
    validOp A.Or A.Bool = True
    validOp _ _ = False
    
    haveOrder :: A.Type -> Bool
    haveOrder = isIntegerType

-- | Checks the types in assignments
checkAssignmentTypes :: Data t => t -> PassM t
checkAssignmentTypes = everywhereASTM checkAssignment
  where
    checkAssignment :: A.Process -> PassM A.Process
    checkAssignment ass@(A.Assign m [v] (A.ExpressionList m' [e]))
      = do trhs <- typeOfExpression e
           tlhs <- typeOfVariable v
           if (tlhs == trhs)
             then return ass
             else do rhs' <- coerceType " in assignment" tlhs trhs e
                     return $ A.Assign m [v] (A.ExpressionList m' [rhs'])
    checkAssignment (A.Assign {}) = dieInternal "Rain checker found occam-style assignment"
    checkAssignment st = return st

