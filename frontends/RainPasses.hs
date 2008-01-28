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

-- | A module containing all the misc Rain-specific passes that must be run on the parsed Rain AST before it can be fed into the shared passes.
module RainPasses where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import CompState
import Errors
import Metadata
import Pass
import Pattern
import RainTypes
import TreeUtils
import Types

-- | An ordered list of the Rain-specific passes to be run.
rainPasses :: [(String,Pass)]
rainPasses = 
     [ ("AST Validity check, Rain #1", excludeNonRainFeatures)
       ,("Resolve Int -> Int64",transformInt)
       ,("Uniquify variable declarations, record declared types and resolve variable names",uniquifyAndResolveVars) --depends on transformInt
       
       ,("Fold all constant expressions",constantFoldPass) -- depends on transformInt and possibly depends on uniquifyAndResolveVars, not sure
       ,("Annotate integer literal types",annnotateIntLiteralTypes) --depends on transformInt and constantFoldPass
       
       ,("Record inferred name types in dictionary",recordInfNameTypes) --depends on uniquifyAndResolveVars and annnotateIntLiteralTypes
       
       ,("Check types in expressions",checkExpressionTypes) 
           --depends on transformInt, uniquifyAndResolveVars, constantFoldPass, annnotateIntLiteralTypes, recordInfNameTypes
       ,("Check types in assignments",checkAssignmentTypes) --depends on uniquifyAndResolveVars, recordInfNameTypes, checkExpressionTypes
       ,("Check types in if/while conditions",checkConditionalTypes) --depends on uniquifyAndResolveVars, recordInfNameTypes, checkExpressionTypes
       ,("Check types in input/output",checkCommTypes) --depends on uniquifyAndResolveVars, recordInfNameTypes, checkExpressionTypes
       ,("Check types in now statements",checkGetTimeTypes) --depends on uniquifyAndResolveVars, recordInfNameTypes
       
       ,("Find and tag the main function",findMain) --depends on uniquifyAndResolveVars
       ,("Check parameters in process calls",matchParamPass) --depends on uniquifyAndResolveVars and recordInfNameTypes and checkExpressionTypes
       ,("Convert seqeach/pareach loops over ranges into simple replicated SEQ/PAR",transformEachRange)
         --depends on uniquifyAndResolveVars and recordInfNameTypes       
       ,("Convert seqeach/pareach loops into classic replicated SEQ/PAR",transformEach) 
         --depends on uniquifyAndResolveVars and recordInfNameTypes, and should be done after transformEachRange
       ,("Convert simple Rain range constructors into more general array constructors",transformRangeRep)
         --must be done after transformEachRange
       ,("Transform Rain functions into the occam form",transformFunction)
         --must be done after transformEach, depends on uniquifyAndResolveVars and recordInfNameTypes
       ,("Pull up par declarations", pullUpParDeclarations) --doesn't depend on anything
       ,("AST Validity check, Rain #2", (\x -> excludeNonRainFeatures x >>= excludeTransformedRainFeatures))
     ]

-- | A pass that transforms all instances of 'A.Int' into 'A.Int64'
transformInt :: Data t => t -> PassM t
transformInt = everywhereM (mkM transformInt')
  where
    transformInt' :: A.Type -> PassM A.Type
    transformInt' A.Int = return A.Int64
    transformInt' t = return t

-- | This pass effectively does three things in one:
--
-- 1. Creates unique names for all declared variables
--
-- 2. Records the type of these declarations into the state 
--
-- 3. Resolves all uses of the name into its unique version
--
-- This may seem like three passes in one, but if you try to separate them out, it just ends up
-- with more confusion and more code.
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
                                                  A.ndNameType = A.VariableName, A.ndType = (A.Declaration m t Nothing),
                                                  A.ndAbbrevMode = am, A.ndPlacement = A.Unplaced}
                    let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
                    return (A.Formal am t newName, scope')
    --Other:
    uniquifyAndResolveVars' s = return s

-- | Helper function for a few of the passes.  Replaces 'A.nameName' of a 'A.Name' if it matches a given 'String'.
replaceNameName :: 
  String     -- ^ The variable name to be replaced.
  -> String  -- ^ The new variable to use instead.
  -> A.Name  -- ^ The name to check.
  -> A.Name  -- ^ The new name, with the 'A.nameName' field replaced if it matched.
replaceNameName find replace n = if (A.nameName n) == find then n {A.nameName = replace} else n

-- | A pass that finds and tags the main process, and also mangles its name (to avoid problems in the C\/C++ backends with having a function called main).
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
    
checkIntegral :: A.LiteralRepr -> Maybe Integer
checkIntegral (A.IntLiteral _ s) = Just $ read s
checkIntegral (A.HexLiteral _ s) = Nothing -- TODO support hex literals
checkIntegral (A.ByteLiteral _ s) = Nothing -- TODO support char literals
checkIntegral _ = Nothing

-- | Transforms seqeach\/pareach loops over things like [0..99] into SEQ i = 0 FOR 100 loops
transformEachRange :: Data t => t -> PassM t
transformEachRange = everywhereM (mkM transformEachRange')
  where
    transformEachRange' :: A.Structured -> PassM A.Structured
    transformEachRange' s@(A.Rep m _ _)
      = case getMatchedItems patt s of 
          Left _ -> return s --Doesn't match, return the original 
          Right items ->
            do repMeta <- castOrDie "repMeta" items
               eachMeta <- castOrDie "eachMeta" items
               loopVar <- castOrDie "loopVar" items
               begin <- castOrDie "begin" items
               end <- castOrDie "end" items
               body <- castOrDie "body" items
               if (isJust $ checkIntegral begin) && (isJust $ checkIntegral end)
                 then return $ A.Rep repMeta (A.For eachMeta loopVar (A.Literal eachMeta A.Int begin) 
                   (A.Literal eachMeta A.Int $ A.IntLiteral eachMeta $ show ((fromJust $ checkIntegral end) - (fromJust $ checkIntegral begin) + 1))
                   ) body
                 else dieP eachMeta "Items in range constructor (x..y) are not integer literals"
      where
        patt = tag3 A.Rep (Named "repMeta" DontCare) (
                 tag3 A.ForEach (Named "eachMeta" DontCare) (Named "loopVar" DontCare) $ 
                   tag2 A.ExprConstr DontCare $ 
                     tag3 A.RangeConstr DontCare (tag3 A.Literal DontCare DontCare $ Named "begin" DontCare) 
                                              (tag3 A.Literal DontCare DontCare $ Named "end" DontCare)
               ) (Named "body" DontCare)
        castOrDie :: (Typeable b) => String -> Items -> PassM b
        castOrDie key items = case castADI (Map.lookup key items) of
          Just y -> return y
          Nothing -> dieP m "Internal error in transformEachRange"
    transformEachRange' s = return s

-- | A pass that changes all the 'A.ForEach' replicators in the AST into 'A.For' replicators.
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

           let newRep = A.For m' loopIndexName (makeConstant m' 0) (A.SizeVariable m' var)
           let s' = A.Spec m'
                 (A.Specification m' loopVar
                   (A.Is m' am loopVarType
                     (A.SubscriptedVariable m' (A.Subscript m' (A.ExprVariable m' (A.Variable m' loopIndexName)))  var)
                   )
                 )
                 s
           return (spec (A.Rep m newRep s'))
    transformEach' s = return s

-- | A pass that changes all the Rain range constructor expressions into the more general array constructor expressions
transformRangeRep :: Data t => t -> PassM t
transformRangeRep = everywhereM (mkM transformRangeRep')
  where
    transformRangeRep' :: A.Expression -> PassM A.Expression
    transformRangeRep' (A.ExprConstr _ (A.RangeConstr m (A.Literal _ _ beginLit) (A.Literal _ _ endLit)))
      = if (isJust $ checkIntegral beginLit) && (isJust $ checkIntegral endLit)
          then transformRangeRep'' m (fromJust $ checkIntegral beginLit) (fromJust $ checkIntegral endLit)
          else dieP m "Items in range constructor (x..y) are not integer literals"
      where
        transformRangeRep'' :: Meta -> Integer -> Integer -> PassM A.Expression
        transformRangeRep'' m begin end 
          = if (end < begin)
              then dieP m $ "End of range is before beginning: " ++ show begin ++ " > " ++ show end
              else do A.Specification _ rep _ <- makeNonceVariable "rep_constr" m A.Int A.VariableName A.ValAbbrev
                      let count = end - begin + 1
                      return $ A.ExprConstr m $ A.RepConstr m 
                        (A.For m rep 
                          (A.Literal m A.Int (A.IntLiteral m $ show begin)) 
                          (A.Literal m A.Int (A.IntLiteral m $ show count))
                        ) (A.ExprVariable m $ A.Variable m rep)
    transformRangeRep' s = return s

transformFunction :: Data t => t -> PassM t
transformFunction = everywhereM (mkM transformFunction')
  where
    transformFunction' :: A.SpecType -> PassM A.SpecType
    transformFunction' (A.Function m specMode types params body)
      = case body of 
          (A.OnlyP _ (A.Seq m' (A.Several m'' statements))) ->
            if (null statements)
              then dieP m "Functions must not have empty bodies"
              else case (last statements) of 
                ret@(A.OnlyEL {}) -> return $
                  (A.Function m specMode types params 
                    (A.ProcThen m' (A.Seq m' (A.Several m'' (init statements))) ret)
                  )
                _ -> dieP m "Functions must have a return statement as their last statement"
          _ -> dieP m "Functions must have seq[uential] bodies"
    transformFunction' s = return s

pullUpParDeclarations :: Data t => t -> PassM t
pullUpParDeclarations = everywhereM (mkM pullUpParDeclarations')
  where
    pullUpParDeclarations' :: A.Process -> PassM A.Process
    pullUpParDeclarations' p@(A.Par m mode inside) 
      = case chaseSpecs inside of
          Just (specs, innerCode) -> return $ A.Seq m $ specs $ A.OnlyP m $ A.Par m mode innerCode
          Nothing -> return p
    pullUpParDeclarations' p = return p
    
    chaseSpecs :: A.Structured -> Maybe (A.Structured -> A.Structured, A.Structured)
    chaseSpecs (A.Spec m spec inner) 
      = case chaseSpecs inner of
          Nothing -> Just (A.Spec m spec,inner)
          Just (trans,inner') -> Just ( (A.Spec m spec) . trans,inner')
    chaseSpecs _ = Nothing

-- | All the items that should have been removed at the end of the Rain passes.
excludeTransformedRainFeatures :: Data t => t -> PassM t
excludeTransformedRainFeatures = excludeConstr
  [ con0 A.Int
   ,con0 A.Any
   ,con3 A.RangeConstr
   ,con3 A.ForEach
  ]

-- | All the items that should not occur in an AST that comes from Rain (up until it goes into the shared passes).
excludeNonRainFeatures :: Data t => t -> PassM t
excludeNonRainFeatures = excludeConstr
  [ con0 A.Real32
   ,con0 A.Real64
   ,con2 A.Counted
   ,con0 A.Timer
   ,con1 A.Port
   ,con3 A.IntrinsicFunctionCall
   ,con2 A.BytesInExpr
   ,con2 A.BytesInType
   ,con3 A.OffsetOf
   ,con0 A.After
   ,con3 A.InCounted
   ,con3 A.OutCounted
   ,con2 A.InputTimerRead
   ,con2 A.InputTimerAfter
   ,con2 A.Place
   ,con3 A.IsChannelArray
   ,con4 A.Retypes
   ,con4 A.RetypesExpr
   ,con0 A.PriPar
   ,con0 A.PlacedPar
   ,con1 A.Stop
   ,con3 A.Processor
   ,con3 A.IntrinsicProcCall
  ]

