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

module RainTypes (checkExpressionTypes,constantFoldPass,performTypeUnification,recordInfNameTypes) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe
import Data.IORef

import qualified AST as A
import CompState
import Errors
import EvalConstants
import Metadata
import Pass
import ShowCode
import Traversal
import Types
import TypeUnification
import UnifyType
import Utils

lookupMapElseMutVar :: UnifyIndex -> PassM (TypeExp A.Type)
lookupMapElseMutVar k
  = do st <- get
       let m = csUnifyLookup st
       case Map.lookup k m of
         Just v -> return v
         Nothing -> do r <- liftIO $ newIORef Nothing
                       let v = MutVar r
                           m' = Map.insert k v m
                       put st {csUnifyLookup = m'}
                       return v

ttte :: String -> (A.Type -> A.Type) -> A.Type -> PassM (TypeExp A.Type)
ttte c f t = typeToTypeExp t >>= \t' -> return $ OperType c (\[x] -> f x) [t']

-- Transforms the given type into a typeexp, such that the only inner types
-- left will be the primitive types (integer types, float types, bool, time).  Arrays
-- (which would require unification of dimensions and such) are not supported,
-- neither are records.
--  User data types should not be present in the input.
typeToTypeExp :: A.Type -> PassM (TypeExp A.Type)
typeToTypeExp (A.List t) = ttte "[]" A.List t
typeToTypeExp (A.Chan A.DirInput at t) = ttte "?" (A.Chan A.DirInput at) t
typeToTypeExp (A.Chan A.DirOutput at t) = ttte "!" (A.Chan A.DirOutput at) t
typeToTypeExp (A.Chan A.DirUnknown at t) = ttte "channel" (A.Chan A.DirUnknown at) t
typeToTypeExp (A.Mobile t) = ttte "MOBILE" A.Mobile t
typeToTypeExp (A.UnknownVarType en)
  = case en of
      Left n -> lookupMapElseMutVar (UnifyIndex (A.nameMeta n, Right n))
      Right (m, i) -> lookupMapElseMutVar (UnifyIndex (m, Left i))
typeToTypeExp (A.UnknownNumLitType m id n)
  = do r <- liftIO . newIORef $ Left [n]
       let v = NumLit r
       st <- get
       let mp = csUnifyLookup st
       put st {csUnifyLookup = Map.insert (UnifyIndex (m,Left id)) v mp}
       return v
typeToTypeExp t = return $ OperType (show t) (const t) []

markUnify :: (Typed a, Typed b) => a  -> b -> PassM ()
markUnify x y
  = do tx <- astTypeOf x
       ty <- astTypeOf y
       tex <- typeToTypeExp tx
       tey <- typeToTypeExp ty
       modify $ \st -> st {csUnifyPairs = (tex,tey) : csUnifyPairs st}


performTypeUnification :: Data t => t -> PassM t
performTypeUnification x
  = do -- First, we copy the known types into the unify map:
       st <- get
       ul <- shift $ csNames st
       put st {csUnifyPairs = [], csUnifyLookup = ul}
       -- Then we markup all the types in the tree:
       x' <- markConditionalTypes
             <.< markParamPass
             <.< markAssignmentTypes
             <.< markCommTypes
             $ x --TODO markup everything else
       -- Then, we do the unification:
       prs <- get >>* csUnifyPairs
       res <- liftIO $ mapM (uncurry unifyType) prs
       mapM (diePC emptyMeta) (fst $ splitEither res)
       return x'
  where
    shift :: Map.Map String A.NameDef -> PassM (Map.Map UnifyIndex UnifyValue)
    shift = liftM (Map.fromList . catMaybes) . mapM shift' . Map.toList
      where
        shift' :: (String, A.NameDef) -> PassM (Maybe (UnifyIndex, UnifyValue))
        shift' (rawName, d) = do mt <- typeOfSpec (A.ndType d)
                                 case mt of
                                   Nothing -> return Nothing
                                   Just t -> do te <- typeToTypeExp t
                                                return $ Just (UnifyIndex (A.ndMeta d, Right name), te)
          where
            name = A.Name {A.nameName = rawName, A.nameMeta = A.ndMeta d, A.nameType
              = A.ndNameType d}

-- | A pass that records inferred types.  Currently the only place where types are inferred is in seqeach\/pareach loops.
recordInfNameTypes :: Data t => t -> PassM t
recordInfNameTypes = everywhereM (mkM recordInfNameTypes')
  where
    recordInfNameTypes' :: A.Replicator -> PassM A.Replicator
    recordInfNameTypes' input@(A.ForEach m n e)
      = do let innerT = A.UnknownVarType $ Left n
           defineName n A.NameDef {A.ndMeta = m, A.ndName = A.nameName n, A.ndOrigName = A.nameName n, 
                                   A.ndNameType = A.VariableName, A.ndType = (A.Declaration m innerT), 
                                   A.ndAbbrevMode = A.Abbrev, A.ndPlacement = A.Unplaced}
           return input
    recordInfNameTypes' r = return r

-- | Folds all constants.
constantFoldPass :: Data t => t -> PassM t
constantFoldPass = applyDepthM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression = (liftM (\(x,_,_) -> x)) . constantFold

-- | Annotates all integer literal types
annotateIntLiteralTypes :: Data t => t -> PassM t
annotateIntLiteralTypes = applyDepthM doExpression
  where
    --Function is separated out to easily provide the type description of Integer
    powOf2 :: Integer -> Integer
    powOf2 x = 2 ^ x
  
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.Literal m t (A.IntLiteral m' s))
      = do t' <-       
             if (t == A.Int64) then --it's a signed literal
              (if (n >= powOf2 63 || n < (-(powOf2 63))) 
                 then dieP m $ "Signed integer literal too large to fit into 64 bits: " ++ s
                 else 
                   if (n < (-(powOf2 31)) || n >= powOf2 31)
                     then return A.Int64
                     else 
                       if (n < (-(powOf2 15)) || n >= powOf2 15)
                         then return A.Int32
                         else
                           if (n < (-(powOf2 7)) || n >= powOf2 7)
                             then return A.Int16
                             else return A.Int8
              )
              else
                dieP m $ "Unsigned literals currently unsupported"
           return $ A.Literal m t' (A.IntLiteral m' s)
      where
        n :: Integer
        n = read s        
    doExpression e = return e

-- | Annotates all list literals and list ranges with their type
annotateListLiteralTypes :: Data t => t -> PassM t
annotateListLiteralTypes = applyDepthM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.Literal m _ (A.ListLiteral m' es))
      = do ts <- mapM astTypeOf es
           sharedT <- case (ts, leastGeneralSharedTypeRain ts) of
             (_, Just t) -> return t
             ([], Nothing) -> return A.Any
             (_, Nothing) -> diePC m' 
               $ formatCode
                   "Can't determine a common type for the list literal from: %"
                   ts
           es' <- mapM (coerceIfNecessary sharedT) (zip ts es)
           return $ A.Literal m (A.List sharedT) $ A.ListLiteral m' es'
    doExpression (A.ExprConstr m (A.RangeConstr m' t b e))
      = do bt <- astTypeOf b
           et <- astTypeOf e
           sharedT <- case leastGeneralSharedTypeRain [bt, et] of
             Just t -> return t
             Nothing -> diePC m'
               $ formatCode
                  "Can't determine a common type for the range from: % %"
                  bt et
           b' <- coerceIfNecessary sharedT (bt, b)
           e' <- coerceIfNecessary sharedT (et, e)
           return $ A.ExprConstr m $ A.RangeConstr m' (A.List sharedT) b' e'
    doExpression e = return e

    coerceIfNecessary :: A.Type -> (A.Type, A.Expression) -> PassM A.Expression
    coerceIfNecessary to (from, e)
      | to == from = return e
      | otherwise = coerceType " in list literal" to from e

-- | A pass that finds all the 'A.ProcCall' and 'A.FunctionCall' in the
-- AST, and checks that the actual parameters are valid inputs, given
-- the 'A.Formal' parameters in the process's type
markParamPass :: Data t => t -> PassM t
markParamPass = checkDepthM2 matchParamPassProc matchParamPassFunc
  where
    --Picks out the parameters of a process call, checks the number is correct, and maps doParam over them
    matchParamPassProc :: Check A.Process
    matchParamPassProc (A.ProcCall m n actualParams)
      = do def <- lookupNameOrError n $ dieP m ("Process name is unknown: \"" ++ (show $ A.nameName n) ++ "\"")
           case A.ndType def of
             A.Proc _ _ expectedParams _ ->
               if (length expectedParams) == (length actualParams)
               then mapM_ (uncurry markUnify) (zip expectedParams actualParams)
               else dieP m $ "Wrong number of parameters given to process call; expected: " ++ show (length expectedParams) ++ " but found: " ++ show (length actualParams)
             _ -> dieP m $ "You cannot run things that are not processes, such as: \"" ++ (show $ A.nameName n) ++ "\""
    matchParamPassProc _ = return ()
    
    --Picks out the parameters of a function call, checks the number is correct, and maps doExpParam over them
    matchParamPassFunc :: Check A.Expression
    matchParamPassFunc (A.FunctionCall m n actualParams)
      = do def <- lookupNameOrError n $ dieP m ("Function name is unknown: \"" ++ (show $ A.nameName n) ++ "\"")
           case A.ndType def of
             A.Function _ _ _ expectedParams _ ->
               if (length expectedParams) == (length actualParams)
               then mapM_ (uncurry markUnify) (zip expectedParams actualParams)
               else dieP m $ "Wrong number of parameters given to function call; expected: " ++ show (length expectedParams) ++ " but found: " ++ show (length actualParams)
             _ -> dieP m $ "Attempt to make a function call with something"
                        ++ " that is not a function: \"" ++ A.nameName n
                        ++ "\"; is actually: " ++ showConstr (toConstr $
                          A.ndType def)
    matchParamPassFunc _ = return ()

--Adds a cast between two types if it is safe to do so, otherwise gives an error
coerceType :: String -> A.Type -> A.Type -> A.Expression -> PassM A.Expression
coerceType customMsg to from item
      = if isImplicitConversionRain from to
          then return $ A.Conversion (findMeta item) A.DefaultConversion to item
          else diePC (findMeta item) $ (liftM concat) $ sequence [formatCode "Could not perform implicit cast from supplied type: % to expected type: %" from to, return customMsg]


-- | Checks the types in expressions
checkExpressionTypes :: Data t => t -> PassM t
checkExpressionTypes = applyDepthM checkExpression
  where
    -- | Checks the types of an expression where at least one type involved
    -- is Time.
    checkTimeExpression :: Meta -> A.DyadicOp -> (A.Type, A.Expression) ->
      (A.Type, A.Expression) -> PassM A.Expression
    checkTimeExpression m op (tlhs, lhs) (trhs, rhs)
      = case (validOpWithTime op tlhs trhs) of
          Nothing -> diePC m $ formatCode
            "Operator: \"%\" is not valid on types: \"%\" and \"%\"" op tlhs trhs
          Just (destLHS, destRHS) -> 
            if    (isImplicitConversionRain tlhs destLHS)
               && (isImplicitConversionRain trhs destRHS)
              then return $ A.Dyadic m op (convert destLHS tlhs lhs)
                                          (convert destRHS trhs rhs)
              else diePC m $ formatCode
                "Operator: \"%\" is not valid on types: \"%\" and \"%\" (implicit conversions not possible)"
                  op tlhs trhs

    checkExpression :: A.Expression -> PassM A.Expression
    checkExpression e@(A.Dyadic m op lhs rhs)
      = do tlhs <- astTypeOf lhs
           trhs <- astTypeOf rhs
           if (tlhs == A.Time || trhs == A.Time)
             -- Expressions with times can have asymmetric types,
             -- so we handle them specially:
             then checkTimeExpression m op (tlhs, lhs) (trhs, rhs)
             else 
               if (tlhs == trhs)
                 then
                   -- Types identical.  At this point we consider whether the
                   -- user is adding two lists (in which case, correct the
                   -- operator), otherwise we just need to check the operator
                   -- is valid on the types (to avoid two channels of the same
                   -- type being added, for example)
                   case (tlhs, op) of
                     (A.List _, A.Plus) -> return $ A.Dyadic m A.Concat lhs rhs 
                     _ -> if validOpSameType op tlhs
                            then return e
                            else diePC m $ formatCode
                              "Operator: \"%\" is not valid on type: \"%\""
                              op tlhs
                   -- Types differ.  If they are integers, we can look for
                   -- a common (more general) type for both of them to be cast
                   -- up into in order to perform the operation.
                 else if (isIntegerType tlhs && isIntegerType trhs) 
                        then case (leastGeneralSharedTypeRain [tlhs,trhs]) of
                               Nothing -> diePC m $ formatCode "Cannot find a suitable type to convert expression to, types are: % and %" tlhs trhs
                               Just t -> if validOpSameType op t then return $ A.Dyadic m op (convert t tlhs lhs) (convert t trhs rhs) else diePC m $
                                 formatCode "Operator: \"%\" is not valid on type: \"%\"" op tlhs
                        else --The operands are not equal, and are not integers, and neither of them is a time type.  Therefore this must be an error:
                          diePC m $ formatCode "Mis-matched types; no operator applies to types: % and %" tlhs trhs
    checkExpression e@(A.Monadic m op rhs)
      = do trhs <- astTypeOf rhs
           if (op == A.MonadicMinus)
             then case trhs of
                    A.Byte -> return $ A.Monadic m op $ convert A.Int16 trhs rhs
                    A.UInt16 -> return $ A.Monadic m op $ convert A.Int32 trhs rhs
                    A.UInt32 -> return $ A.Monadic m op $ convert A.Int64 trhs rhs
                    A.UInt64 -> diePC m $ formatCode "Cannot apply unary minus to type: % because there is no type large enough to safely contain the result" trhs
                    _ -> if (isIntegerType trhs) then return e else diePC m $ formatCode "Trying to apply unary minus to non-integer type: %" trhs
             else if (op == A.MonadicNot)
                    then
                      case trhs of
                        A.Bool -> return e
                        _ -> diePC m $ formatCode "Cannot apply unary not to non-boolean type: %" trhs
                    else dieP m $ "Invalid Rain operator: \"" ++ show op ++ "\""
    checkExpression e@(A.Conversion m cm dest rhs)
      = do src <- astTypeOf rhs
           if (src == dest)
             then return e
             else if isImplicitConversionRain src dest
                    then return e
                    else diePC m $ formatCode "Invalid cast from: % to: %"
                      src dest
    checkExpression e = return e

    convert :: A.Type -> A.Type -> A.Expression -> A.Expression
    convert dest src e = if (dest == src)
                           then e
                           else A.Conversion (findMeta e) A.DefaultConversion dest e

    validOpSameType :: A.DyadicOp -> A.Type -> Bool
    validOpSameType A.Plus t = isIntegerType t
    validOpSameType A.Minus t = isIntegerType t
    validOpSameType A.Times t = isIntegerType t && t /= A.Time
    validOpSameType A.Div t = isIntegerType t && t /= A.Time
    validOpSameType A.Rem t = isIntegerType t && t /= A.Time
    validOpSameType A.Eq _ = True
    validOpSameType A.NotEq _ = True
    validOpSameType A.Less t = haveOrder t
    validOpSameType A.LessEq t = haveOrder t
    validOpSameType A.More t = haveOrder t
    validOpSameType A.MoreEq t = haveOrder t
    validOpSameType A.And A.Bool = True
    validOpSameType A.Or A.Bool = True
    validOpSameType _ _ = False
    
    -- | Takes an operator, the types of LHS and RHS, and returns Nothing if no cast will fix it,
    -- or Just (needTypeLHS,needTypeRHS) for what types will be okay
    validOpWithTime :: A.DyadicOp -> A.Type -> A.Type -> Maybe (A.Type,A.Type)
    validOpWithTime A.Times A.Time _ = Just (A.Time, A.Int64)
    validOpWithTime A.Times _ A.Time = Just (A.Int64, A.Time)
    validOpWithTime A.Div A.Time _ = Just (A.Time, A.Int64)
    --Any other operators involving Time are symmetric:
    validOpWithTime op tlhs trhs = if (tlhs == trhs && validOpSameType op tlhs) then Just (tlhs,trhs) else Nothing
    
    
    haveOrder :: A.Type -> Bool
    haveOrder t = (isIntegerType t) || (t == A.Time)

-- | Checks the types in assignments
markAssignmentTypes :: Data t => t -> PassM t
markAssignmentTypes = checkDepthM checkAssignment
  where
    checkAssignment :: Check A.Process
    checkAssignment (A.Assign m [v] (A.ExpressionList _ [e]))
      = do am <- abbrevModeOfVariable v
           when (am == A.ValAbbrev) $
             diePC m $ formatCode "Cannot assign to a constant variable: %" v
           markUnify v e
    checkAssignment (A.Assign m _ _) = dieInternal (Just m,"Rain checker found occam-style assignment")
    checkAssignment st = return ()

-- | Checks the types in if and while conditionals
markConditionalTypes :: Data t => t -> PassM t
markConditionalTypes = checkDepthM2 checkWhile checkIf
  where
    checkWhile :: Check A.Process
    checkWhile w@(A.While m exp _)
      = markUnify exp A.Bool
    checkWhile _ = return ()
    
    checkIf :: Check A.Choice
    checkIf c@(A.Choice m exp _)
      = markUnify exp A.Bool

-- | Checks the types in inputs and outputs, including inputs in alts
markCommTypes :: Data t => t -> PassM t
markCommTypes = checkDepthM2 checkInputOutput checkAltInput
  where
    checkInput :: A.Variable -> A.Variable -> Meta -> a -> PassM ()
    checkInput chanVar destVar m p
      = astTypeOf destVar >>= markUnify chanVar . A.Chan A.DirInput (A.ChanAttributes
        False False)

    checkWait :: Check A.InputMode
    checkWait (A.InputTimerFor m exp) = markUnify A.Time exp
    checkWait (A.InputTimerAfter m exp) = markUnify A.Time exp
    checkWait (A.InputTimerRead m (A.InVariable _ v)) = markUnify A.Time v
    checkWait _ = return ()

    checkInputOutput :: Check A.Process
    checkInputOutput p@(A.Input m chanVar (A.InputSimple _ [A.InVariable _ destVar]))
      = checkInput chanVar destVar m p
    checkInputOutput (A.Input _ _ im@(A.InputTimerFor {})) = checkWait im
    checkInputOutput (A.Input _ _ im@(A.InputTimerAfter {})) = checkWait im
    checkInputOutput (A.Input _ _ im@(A.InputTimerRead {})) = checkWait im
    checkInputOutput p@(A.Output m chanVar [A.OutExpression m' srcExp])
      = astTypeOf srcExp >>= markUnify chanVar . A.Chan A.DirOutput (A.ChanAttributes
        False False)
    checkInputOutput _ = return ()

    checkAltInput :: Check A.Alternative
    checkAltInput a@(A.Alternative m _ chanVar (A.InputSimple _ [A.InVariable _ destVar]) body)
      = checkInput chanVar destVar m a
    checkAltInput (A.Alternative m _ _ im@(A.InputTimerFor {}) _) = checkWait im
    checkAltInput (A.Alternative m _ _ im@(A.InputTimerAfter {}) _) = checkWait im
    checkAltInput _ = return ()
