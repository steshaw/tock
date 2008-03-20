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
import qualified Properties as Prop
import RainTypes
import TreeUtils
import Types

--TODO change this whole module to stop using everywhere

-- | An ordered list of the Rain-specific passes to be run.
rainPasses :: [Pass]
rainPasses = makePassesDep' ((== FrontendRain) . csFrontend)
     [ ("AST Validity check, Rain #1", excludeNonRainFeatures, [], []) -- TODO work out some dependencies
       ,("Resolve Int -> Int64", transformInt, [], [Prop.noInt])
       ,("Uniquify variable declarations, record declared types and resolve variable names",
           uniquifyAndResolveVars, [Prop.noInt], namesDone)
            
       ,("Fold all constant expressions", constantFoldPass, [Prop.noInt] ++ namesDone, [Prop.constantsFolded, Prop.constantsChecked])
       ,("Annotate integer literal types", annnotateIntLiteralTypes, [Prop.noInt] ++ namesDone, [Prop.intLiteralsInBounds])
       
       ,("Record inferred name types in dictionary", recordInfNameTypes, namesDone ++ [Prop.intLiteralsInBounds], [Prop.inferredTypesRecorded])
       
       ,("Check types in expressions",checkExpressionTypes, namesDone ++ [Prop.noInt, Prop.constantsFolded, Prop.intLiteralsInBounds, Prop.inferredTypesRecorded], [Prop.expressionTypesChecked]) 
       ,("Check types in assignments", checkAssignmentTypes, typesDone ++ [Prop.expressionTypesChecked], [Prop.processTypesChecked])
       ,("Check types in if/while conditions",checkConditionalTypes, typesDone ++ [Prop.expressionTypesChecked], [Prop.processTypesChecked])
       ,("Check types in input/output",checkCommTypes, typesDone ++ [Prop.expressionTypesChecked], [Prop.processTypesChecked])
       ,("Check types in now statements",checkGetTimeTypes, typesDone, [Prop.processTypesChecked])
       ,("Check parameters in process calls", matchParamPass, typesDone, [Prop.processTypesChecked])
       
       ,("Find and tag the main function", findMain, namesDone, [Prop.mainTagged])
       ,("Convert seqeach/pareach loops over ranges into simple replicated SEQ/PAR",
         transformEachRange, typesDone ++ [Prop.constantsFolded], [Prop.eachRangeTransformed])
       ,("Pull up foreach-expressions", pullUpForEach,
         typesDone ++ [Prop.constantsFolded],
         [Prop.eachTransformed])
       ,("Convert simple Rain range constructors into more general array constructors",transformRangeRep, typesDone ++ [Prop.eachRangeTransformed], [Prop.rangeTransformed])
       ,("Transform Rain functions into the occam form",checkFunction, typesDone, [])
         --TODO add an export property.  Maybe check other things too (lack of comms etc -- but that could be combined with occam?)
       ,("Pull up par declarations", pullUpParDeclarations, [], [Prop.rainParDeclarationsPulledUp])
     ]
  where
    namesDone :: [Property]
    namesDone = [Prop.declaredNamesResolved, Prop.declarationTypesRecorded, Prop.declarationsUnique]

    typesDone :: [Property]
    typesDone = namesDone ++ [Prop.inferredTypesRecorded]


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
--
-- This pass works because everywhereM goes bottom-up, so declarations are
--resolved from the bottom upwards.
uniquifyAndResolveVars :: Data t => t -> PassM t
uniquifyAndResolveVars = everywhereM (mk1M uniquifyAndResolveVars')
  where
    uniquifyAndResolveVars' :: Data a => A.Structured a -> PassM (A.Structured a)
    
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

    -- replicator names have their types recorded later, but are
    -- uniquified and resolved here
    uniquifyAndResolveVars' (A.Rep m (A.ForEach m' n e) scope)
      = do n' <- makeNonce $ A.nameName n
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return $ A.Rep m (A.ForEach m' (n {A.nameName = n'}) e) scope'
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
transformEachRange = doGeneric `ext1M` doStructured
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric transformEachRange
    
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Rep repMeta (A.ForEach eachMeta loopVar (A.ExprConstr
      _ (A.RangeConstr _ _ begin end))) body)
        =   do body' <- doStructured body
               return $ A.Rep repMeta (A.For eachMeta loopVar begin
                 (addOne $ subExprs end begin)) body'
    doStructured s = doGeneric s

-- | A pass that changes all the Rain range constructor expressions into the more general array constructor expressions
transformRangeRep :: Data t => t -> PassM t
transformRangeRep = doGeneric `extM` doExpression
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric transformRangeRep
    
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.ExprConstr _ (A.RangeConstr m t (A.Literal _ _ beginLit) (A.Literal _ _ endLit)))
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
                      return $ A.ExprConstr m $ A.RepConstr m t
                        (A.For m rep 
                          (A.Literal m A.Int (A.IntLiteral m $ show begin)) 
                          (A.Literal m A.Int (A.IntLiteral m $ show count))
                        ) (A.ExprVariable m $ A.Variable m rep)
    doExpression e = doGeneric e

checkFunction :: Data t => t -> PassM t
checkFunction = everywhereM (mkM checkFunction')
  where
    checkFunction' :: A.Specification -> PassM A.Specification
    checkFunction' spec@(A.Specification _ n (A.Function m _ _ _ (Right body)))
      = case body of 
          (A.Seq m' (A.Several m'' statements)) ->
            if (null statements)
              then dieP m "Functions must not have empty bodies"
              else case (last statements) of
                (A.Only _ (A.Assign _ [A.Variable _ dest] _)) -> if A.nameName n == A.nameName dest then return spec else
                  dieP m "Functions must have a return statement as their last statement."
                _ -> dieP m "Functions must have a return statement as their last statement"
          _ -> dieP m "Functions must have seq[uential] bodies"
    checkFunction' s = return s

-- | Pulls up the list expression into a variable.
-- This is done no matter how simple the expression is; when we reach the
-- backend we need it to be a variable so we can use begin() and end() (in
-- C++); these will only be valid if exactly the same list is used
-- throughout the loop.
pullUpForEach :: Data t => t -> PassM t
pullUpForEach = doGeneric `ext1M` doStructured
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric pullUpForEach

    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Rep m (A.ForEach m' loopVar loopExp) s)
     = do (extra, loopExp') <- case loopExp of
            A.ExprVariable {} -> return (id, loopExp)
            _ -> do t <- typeOfExpression loopExp
                    spec@(A.Specification _ n _) <- makeNonceIsExpr
                      "loop_expr" m' t loopExp
                    return (A.Spec m' spec, A.ExprVariable m' (A.Variable m' n))
          s' <- doStructured s
          return $ extra $ A.Rep m (A.ForEach m' loopVar loopExp') s'
    doStructured s = doGeneric s
      
    
pullUpParDeclarations :: Data t => t -> PassM t
pullUpParDeclarations = everywhereM (mkM pullUpParDeclarations')
  where
    pullUpParDeclarations' :: A.Process -> PassM A.Process
    pullUpParDeclarations' p@(A.Par m mode inside) 
      = case chaseSpecs inside of
          Just (specs, innerCode) -> return $ A.Seq m $ specs $ A.Only m $ A.Par m mode innerCode
          Nothing -> return p
    pullUpParDeclarations' p = return p
    
    chaseSpecs :: A.Structured A.Process -> Maybe (A.Structured A.Process -> A.Structured A.Process, A.Structured A.Process)
    chaseSpecs (A.Spec m spec inner) 
      = case chaseSpecs inner of
          Nothing -> Just (A.Spec m spec,inner)
          Just (trans,inner') -> Just ( (A.Spec m spec) . trans,inner')
    chaseSpecs _ = Nothing

-- | All the items that should not occur in an AST that comes from Rain (up until it goes into the shared passes).
excludeNonRainFeatures :: (Data t, CSMR m) => t -> m t
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

