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

module RainPasses where

import TestUtil
import qualified AST as A
import Pass
import Data.Generics
import qualified Data.Map as Map
import Control.Monad.State
import Types
import CompState
import Errors
import Metadata

rainPasses :: [(String,Pass)]
rainPasses = 
     [ ("Resolve Int -> Int64",transformInt)
       ,("Uniquify variable declarations, record declared types and resolve variable names",uniquifyAndResolveVars)
       ,("Record inferred name types in dictionary",recordInfNameTypes) --depends on uniquifyAndResolveVars
       ,("Find and tag the main function",findMain) --depends on uniquifyAndResolveVars
       ,("Check parameters in process calls",matchParamPass) --depends on uniquifyAndResolveVars and recordInfNameTypes
       ,("Convert seqeach/pareach loops into classic replicated SEQ/PAR",transformEach)
     ]

transformInt :: Data t => t -> PassM t
transformInt = everywhereM (mkM transformInt')
  where
    transformInt' :: A.Type -> PassM A.Type
    transformInt' A.Int = return A.Int64
    transformInt' t = return t

-- | This pass effectively does three things in one:
--
-- 1. Creates unique names for all declared variables
-- 2. Records the type of these declarations into the state 
-- 3. Resolves all uses of the name into its unique version
--
-- This may seem like three passes in one, but if you try to separate them out, it just ends up
-- with more confusion and more code, instead of less.
uniquifyAndResolveVars :: Data t => t -> PassM t
uniquifyAndResolveVars = everywhereM (mkM uniquifyAndResolveVars')
  where
    uniquifyAndResolveVars' :: A.Structured -> PassM A.Structured
    
    --Variable declarations:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n decl@(A.Declaration {})) scope) 
      = do n' <- makeNonce $ A.nameName n
           defineName (n {A.nameName = n'}) A.NameDef {A.ndMeta = m', A.ndName = n', A.ndOrigName = A.nameName n, 
                                                       A.ndNameType = A.VariableName, A.ndType = decl, 
                                                       A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return $ A.Spec m (A.Specification m' n {A.nameName = n'} decl) scope'
           
    --Processes:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n (A.Proc m'' procMode params procBody)) scope) 
      = do (params',procBody') <- doFormals params procBody
           let newProc = (A.Proc m'' procMode params' procBody')
           defineName n A.NameDef {A.ndMeta = m', A.ndName = A.nameName n, A.ndOrigName = A.nameName n,
                                   A.ndNameType = A.ProcName, A.ndType = newProc, 
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return $ A.Spec m (A.Specification m' n newProc) scope
           where
             --This function is like applying mapM to doFormals', but we need to let each doFormals' call in turn
             --transform the scope of the formals.  This could possibly be done by using a StateT monad with the scope,
             --but this method works just as well:
             doFormals :: Data t => [A.Formal] -> t -> PassM ([A.Formal],t)
             doFormals [] s = return ([],s)
             doFormals (f:fs) s = do (f',s') <- doFormals' f s
                                     (fs',s'') <- doFormals fs s'
                                     return ((f':fs'),s'')
             doFormals' :: Data t => A.Formal -> t -> PassM (A.Formal,t)
             doFormals' (A.Formal am t n) scope
               = do n' <- makeNonce $ A.nameName n
                    let newName = (n {A.nameName = n'})
                    let m = A.nameMeta n
                    defineName newName A.NameDef {A.ndMeta = m, A.ndName = n', A.ndOrigName = A.nameName n, 
                                                  A.ndNameType = A.VariableName, A.ndType = (A.Declaration m t),
                                                  A.ndAbbrevMode = am, A.ndPlacement = A.Unplaced}
                    let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
                    return (A.Formal am t newName, scope')
    --Other:
    uniquifyAndResolveVars' s = return s

--Helper function for a few of the passes:
replaceNameName :: String -> String -> A.Name -> A.Name
replaceNameName find replace n = if (A.nameName n) == find then n {A.nameName = replace} else n

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

findMain :: Data t => t -> PassM t
--Because findMain runs after uniquifyAndResolveVars, the types of all the process will have been recorded
--Therefore this pass doesn't actually need to walk the tree, it just has to look for a process named "main"
--in the CompState, and pull it out into csMainLocals
findMain x = do newMainName <- makeNonce "main_"
                modify (findMain' newMainName)
                everywhereM (mkM $ return . (replaceNameName "main" newMainName)) x
  where
    --We have to mangle the main name because otherwise it will cause problems on some backends (including C and C++)
    findMain' :: String -> CompState -> CompState 
    findMain' newn st = case (Map.lookup "main" (csNames st)) of
      Just n -> st {csNames = changeMainName newn (csNames st) , csMainLocals = [(newn,A.Name {A.nameName = newn, A.nameMeta = A.ndMeta n, A.nameType = A.ndNameType n})]}
      Nothing -> st 
    changeMainName :: String -> Map.Map String A.NameDef -> Map.Map String A.NameDef
    changeMainName n m = case (Map.lookup "main" m) of
      Nothing -> m
      Just nd -> ((Map.insert n (nd {A.ndName = n})) . (Map.delete "main")) m     
    
-- | Finds all the ProcCall in the AST, and checks that the actual parameters are valid inputs, given the Formal parameters in the process's type
matchParamPass :: Data t => t -> PassM t
matchParamPass = everywhereM (mkM matchParamPass')
  where
    matchParamPass' :: A.Process -> PassM A.Process
    matchParamPass' (A.ProcCall m n actualParams)
      = do def <- lookupNameOrError n $ dieP m ("Process name is unknown: \"" ++ (show $ A.nameName n) ++ "\"")
           case A.ndType def of
             A.Proc _ _ expectedParams _ ->
               if (length expectedParams) == (length actualParams)
               then do transActualParams <- mapM (doParam m (A.nameName n)) (zip3 [0..] expectedParams actualParams)
                       return $ A.ProcCall m n transActualParams
               else dieP m $ "Wrong number of parameters given to process call; expected: " ++ show (length expectedParams) ++ " but found: " ++ show (length actualParams)
             _ -> dieP m $ "You cannot run things that are not processes, such as: \"" ++ (show $ A.nameName n) ++ "\""
    matchParamPass' p = return p

    doParam :: Meta -> String -> (Int,A.Formal, A.Actual) -> PassM A.Actual
    doParam m n (index, A.Formal formalAbbrev formalType formalName, A.ActualVariable _ _ v)
      = do actualType <- typeOfVariable v
           if (actualType == formalType)
             then return $ A.ActualVariable formalAbbrev formalType v
             else doActualCast index formalType actualType (A.ExprVariable (findMeta v) v )
    doParam m n (index, A.Formal formalAbbrev formalType formalName, A.ActualExpression _ e)
      = do actualType <- typeOfExpression e
           if (actualType == formalType)
             then return $ A.ActualExpression formalType e
             else doActualCast index formalType actualType e

    doActualCast :: Int -> A.Type -> A.Type -> A.Expression -> PassM A.Actual
    doActualCast index to from item
      = if isSafeConversion from to
          then return $ A.ActualExpression to $ A.Conversion (findMeta item) A.DefaultConversion to item
          else dieP (findMeta item) $ "Could not perform implicit cast from supplied type: " ++ (show from) ++
            " to expected type: " ++ (show to) ++ " for parameter (zero-based): " ++ (show index)

transformEach :: Data t => t -> PassM t
transformEach = everywhereM (mkM transformEach')
  where
    transformEach' :: A.Structured -> PassM A.Structured
    transformEach' (A.Rep m (A.ForEach m' loopVar loopExp) s)
      = do (spec,var,am) <- case loopExp of
             (A.ExprVariable _ v) -> return (id,v,A.Abbrev)
             _ -> do t <- typeOfExpression loopExp
                     spec@(A.Specification _ n' _) <- makeNonceIsExpr "loopVar" m t loopExp 
                     return (A.Spec m spec,A.Variable m n',A.ValAbbrev)
           --spec is a function A.Structured -> A.Structured, var is an A.Variable
           
           loopVarType <- typeOfName loopVar
           A.Specification _ loopIndexName _ <- makeNonceVariable "loopIndex" m' A.Int64 A.VariableName A.Original

           let newRep = A.For m' loopIndexName (intLiteral 0) (A.SizeVariable m' var)
           let s' = A.Spec m'
                 (A.Specification m' loopVar
                   (A.Is m' am loopVarType
                     (A.SubscriptedVariable m' (A.Subscript m' (A.ExprVariable m' (A.Variable m' loopIndexName)))  var)
                   )
                 )
                 s
           return (spec (A.Rep m newRep s'))
    transformEach' s = return s
