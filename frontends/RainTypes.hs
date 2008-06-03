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

module RainTypes (constantFoldPass,performTypeUnification,recordInfNameTypes) where

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.IORef

import qualified AST as A
import CompState
import Errors
import EvalConstants
import Metadata
import Pass
import qualified Properties as Prop
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
                       let UnifyIndex (mt,_) = k
                           v = MutVar mt r
                           m' = Map.insert k v m
                       put st {csUnifyLookup = m'}
                       return v

ttte :: Meta -> String -> (A.Type -> A.Type) -> A.Type -> PassM (TypeExp A.Type)
ttte m c f t = typeToTypeExp m t >>= \t' -> return $ OperType m c (\[x] -> f x) [t']

-- Transforms the given type into a typeexp, such that the only inner types
-- left will be the primitive types (integer types, float types, bool, time).  Arrays
-- (which would require unification of dimensions and such) are not supported,
-- neither are records.
--  User data types should not be present in the input.
typeToTypeExp :: Meta -> A.Type -> PassM (TypeExp A.Type)
typeToTypeExp m (A.List t) = ttte m "[]" A.List t
typeToTypeExp m (A.Chan A.DirInput at t) = ttte m "?" (A.Chan A.DirInput at) t
typeToTypeExp m (A.Chan A.DirOutput at t) = ttte m "!" (A.Chan A.DirOutput at) t
typeToTypeExp m (A.Chan A.DirUnknown at t) = ttte m "channel" (A.Chan A.DirUnknown at) t
typeToTypeExp m (A.Mobile t) = ttte m "MOBILE" A.Mobile t
typeToTypeExp _ (A.UnknownVarType en)
  = case en of
      Left n -> lookupMapElseMutVar (UnifyIndex (A.nameMeta n, Right n))
      Right (m, i) -> lookupMapElseMutVar (UnifyIndex (m, Left i))
typeToTypeExp _ (A.UnknownNumLitType m id n)
  = do r <- liftIO . newIORef $ Left [(m,n)]
       let v = NumLit m r
       st <- get
       let mp = csUnifyLookup st
       put st {csUnifyLookup = Map.insert (UnifyIndex (m,Left id)) v mp}
       return v
typeToTypeExp m t = return $ OperType m (show t) (const t) []

markUnify :: (ASTTypeable a, ASTTypeable b, Data a, Data b) => a -> b -> PassM ()
markUnify x y
  = do tx <- astTypeOf x
       ty <- astTypeOf y
       tex <- typeToTypeExp (findMeta x) tx
       tey <- typeToTypeExp (findMeta y) ty
       modify $ \st -> st {csUnifyPairs = (tex,tey) : csUnifyPairs st}


performTypeUnification :: Pass
performTypeUnification = rainOnlyPass "Rain Type Checking"
  ([Prop.noInt] ++ Prop.agg_namesDone)
  [Prop.expressionTypesChecked, Prop.functionTypesChecked, Prop.processTypesChecked, Prop.retypesChecked]
  (\x -> do -- First, we copy the known types into the unify map:
       st <- get
       ul <- shift $ csNames st
       put st {csUnifyPairs = [], csUnifyLookup = ul}
       -- Then we markup all the types in the tree:
       x' <- markConditionalTypes
             <.< markParamPass
             <.< markAssignmentTypes
             <.< markCommTypes
             <.< markReplicators
             <.< markExpressionTypes
             $ x
       -- Then, we do the unification:
       prs <- get >>* csUnifyPairs
       mapM_ (uncurry unifyType) prs
       -- Now put the types back in a map, and replace them through the tree:
       l <- get >>* csUnifyLookup
       ts <- mapMapM (\v -> fromTypeExp v) l
       get >>= substituteUnknownTypes ts >>= put
       substituteUnknownTypes ts x')
  where
    shift :: Map.Map String A.NameDef -> PassM (Map.Map UnifyIndex UnifyValue)
    shift = liftM (Map.fromList . catMaybes) . mapM shift' . Map.toList
      where
        shift' :: (String, A.NameDef) -> PassM (Maybe (UnifyIndex, UnifyValue))
        shift' (rawName, d) = do mt <- typeOfSpec (A.ndSpecType d)
                                 case mt of
                                   Nothing -> return Nothing
                                   Just t -> do te <- typeToTypeExp (A.ndMeta d) t
                                                return $ Just (UnifyIndex (A.ndMeta d, Right name), te)
          where
            name = A.Name {A.nameName = rawName, A.nameMeta = A.ndMeta d}

substituteUnknownTypes :: Map.Map UnifyIndex A.Type -> PassType
substituteUnknownTypes mt = applyDepthM sub
  where
    sub :: A.Type -> PassM A.Type
    sub (A.UnknownVarType (Left n)) = lookup $ UnifyIndex (A.nameMeta n, Right n)
    sub (A.UnknownVarType (Right (m,i))) = lookup $ UnifyIndex (m,Left i)
    sub (A.UnknownNumLitType m i _) = lookup $ UnifyIndex (m, Left i)
    sub t = return t

    lookup :: UnifyIndex -> PassM A.Type
    lookup u@(UnifyIndex(m,_)) = case Map.lookup u mt of
      Just t -> return t
      Nothing -> dieP m "Could not deduce type"

-- | A pass that records inferred types.  Currently the only place where types are inferred is in seqeach\/pareach loops.
recordInfNameTypes :: Pass
recordInfNameTypes = rainOnlyPass "Record inferred name types in dictionary"
  (Prop.agg_namesDone \\ [Prop.inferredTypesRecorded]) [Prop.inferredTypesRecorded]
  (checkDepthM recordInfNameTypes')
  where
    recordInfNameTypes' :: Check A.Replicator
    recordInfNameTypes' input@(A.ForEach m n e)
      = let innerT = A.UnknownVarType $ Left n in
           defineName n A.NameDef { A.ndMeta = m
                                  , A.ndName = A.nameName n
                                  , A.ndOrigName = A.nameName n
                                  , A.ndSpecType = A.Declaration m innerT
                                  , A.ndAbbrevMode = A.Abbrev
                                  , A.ndPlacement = A.Unplaced
                                  }
    recordInfNameTypes' _ = return ()

markReplicators :: PassType
markReplicators = checkDepthM mark
  where
    mark :: Check A.Replicator
    mark (A.ForEach _m n e)
      = astTypeOf n >>= \t -> markUnify (A.List t) e

-- | Folds all constants.
constantFoldPass :: Pass
constantFoldPass = rainOnlyPass "Fold all constant expressions"
  ([Prop.noInt] ++ Prop.agg_namesDone ++ [Prop.inferredTypesRecorded])
  [Prop.constantsFolded, Prop.constantsChecked]
  (applyDepthM doExpression)
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression = (liftM (\(x,_,_) -> x)) . constantFold

-- | A pass that finds all the 'A.ProcCall' and 'A.FunctionCall' in the
-- AST, and checks that the actual parameters are valid inputs, given
-- the 'A.Formal' parameters in the process's type
markParamPass :: PassType
markParamPass = checkDepthM2 matchParamPassProc matchParamPassFunc
  where
    --Picks out the parameters of a process call, checks the number is correct, and maps doParam over them
    matchParamPassProc :: Check A.Process
    matchParamPassProc (A.ProcCall m n actualParams)
      = do def <- lookupNameOrError n $ dieP m ("Process name is unknown: \"" ++ (show $ A.nameName n) ++ "\"")
           case A.ndSpecType def of
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
           case A.ndSpecType def of
             A.Function _ _ _ expectedParams _ ->
               if (length expectedParams) == (length actualParams)
               then mapM_ (uncurry markUnify) (zip expectedParams actualParams)
               else dieP m $ "Wrong number of parameters given to function call; expected: " ++ show (length expectedParams) ++ " but found: " ++ show (length actualParams)
             _ -> dieP m $ "Attempt to make a function call with something"
                        ++ " that is not a function: \"" ++ A.nameName n
                        ++ "\"; is actually: " ++ showConstr (toConstr $
                          A.ndSpecType def)
    matchParamPassFunc _ = return ()

-- | Checks the types in expressions
markExpressionTypes :: PassType
markExpressionTypes = checkDepthM checkExpression
  where
    -- TODO also check in a later pass that the op is valid
    checkExpression :: Check A.Expression
    checkExpression (A.Dyadic _ _ lhs rhs)
      = markUnify lhs rhs
    checkExpression (A.Literal _ t (A.ListLiteral _ es))
      = do ts <- mapM astTypeOf es
           mapM_ (markUnify t . A.List) ts
    checkExpression (A.ExprConstr _ con)
      = case con of
          A.RangeConstr _ t e e' ->
            do astTypeOf e >>= markUnify t . A.List
               astTypeOf e' >>= markUnify t . A.List
          A.RepConstr _ t _ e ->
            astTypeOf e >>= markUnify t . A.List
    checkExpression _ = return ()

-- | Checks the types in assignments
markAssignmentTypes :: PassType
markAssignmentTypes = checkDepthM checkAssignment
  where
    checkAssignment :: Check A.Process
    checkAssignment (A.Assign m [v] (A.ExpressionList _ [e]))
      = do am <- abbrevModeOfVariable v
           when (am == A.ValAbbrev) $
             diePC m $ formatCode "Cannot assign to a constant variable: %" v
           -- Assignments also includes assignments to function names,
           -- so we need a little extra logic:
           case v of
             A.Variable _ n ->
               do st <- specTypeOfName n
                  case st of
                    A.Function _ _ [t] _ _ -> markUnify t e
                    _ -> markUnify v e
             _ -> markUnify v e
    checkAssignment (A.Assign m _ _) = dieInternal (Just m,"Rain checker found occam-style assignment")
    checkAssignment st = return ()

-- | Checks the types in if and while conditionals
markConditionalTypes :: PassType
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
markCommTypes :: PassType
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
