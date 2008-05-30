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

-- | A module containing all the misc Rain-specific passes that must be run on the parsed Rain AST before it can be fed into the shared passes.
module RainPasses where

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import CompState
import Errors
import ImplicitMobility
import Pass
import qualified Properties as Prop
import RainTypes
import SimplifyTypes
import Traversal
import TreeUtils
import Types

--TODO change this whole module to stop using everywhere

-- | An ordered list of the Rain-specific passes to be run.
rainPasses :: [Pass]
rainPasses = let f = makePassesDep' ((== FrontendRain) . csFrontend) in f
     [ ("AST Validity check, Rain #1", excludeNonRainFeatures, [], []) -- TODO work out some dependencies
       ,("Dummy Rain pass", return, [], [Prop.retypesChecked])
       ,("Resolve Int -> Int64", transformInt, [], [Prop.noInt])
       ,("Uniquify variable declarations, record declared types and resolve variable names",
           uniquifyAndResolveVars, [Prop.noInt], Prop.agg_namesDone \\ [Prop.inferredTypesRecorded])
       ,("Record inferred name types in dictionary", recordInfNameTypes,
           Prop.agg_namesDone \\ [Prop.inferredTypesRecorded], [Prop.inferredTypesRecorded])
            
       ,("Rain Type Checking", performTypeUnification, [Prop.noInt] ++ Prop.agg_namesDone,
         [Prop.expressionTypesChecked, Prop.functionTypesChecked, Prop.processTypesChecked,
          Prop.retypesChecked])
       ,("Fold all constant expressions", constantFoldPass, [Prop.noInt] ++ Prop.agg_namesDone
            ++ [Prop.inferredTypesRecorded], [Prop.constantsFolded, Prop.constantsChecked])

     ] ++ enablePassesWhen ((== FrontendRain) . csFrontend) simplifyTypes ++ f [
       
        ("Find and tag the main function", findMain, Prop.agg_namesDone, [Prop.mainTagged])
       ,("Convert seqeach/pareach loops over ranges into simple replicated SEQ/PAR",
         transformEachRange, Prop.agg_typesDone ++ [Prop.constantsFolded], [Prop.eachRangeTransformed])
       ,("Pull up foreach-expressions", pullUpForEach,
         Prop.agg_typesDone ++ [Prop.constantsFolded],
         [Prop.eachTransformed])
       ,("Convert simple Rain range constructors into more general array constructors",transformRangeRep, Prop.agg_typesDone ++ [Prop.eachRangeTransformed], [Prop.rangeTransformed])
       ,("Transform Rain functions into the occam form",checkFunction, Prop.agg_typesDone, [])
         --TODO add an export property.  Maybe check other things too (lack of comms etc -- but that could be combined with occam?)
       ,("Pull up par declarations", pullUpParDeclarations, [], [Prop.rainParDeclarationsPulledUp])

       ,("Implicit mobility pass", implicitMobility, [], [])
     ]

-- | A pass that transforms all instances of 'A.Int' into 'A.Int64'
transformInt :: PassType
transformInt = applyDepthM transformInt'
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
uniquifyAndResolveVars :: PassType
uniquifyAndResolveVars = applyDepthSM uniquifyAndResolveVars'
  where
    uniquifyAndResolveVars' :: Data a => A.Structured a -> PassM (A.Structured a)
    
    --Variable declarations:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n decl@(A.Declaration {})) scope) 
      = do n' <- makeNonce $ A.nameName n
           defineName (n {A.nameName = n'}) A.NameDef {A.ndMeta = m', A.ndName = n', A.ndOrigName = A.nameName n, 
                                                       A.ndNameType = A.VariableName, A.ndSpecType = decl, 
                                                       A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return $ A.Spec m (A.Specification m' n {A.nameName = n'} decl) scope'
           
    --Processes:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n (A.Proc m'' procMode params procBody)) scope) 
      = do (params',procBody') <- doFormals params procBody
           let newProc = (A.Proc m'' procMode params' procBody')
           defineName n A.NameDef {A.ndMeta = m', A.ndName = A.nameName n, A.ndOrigName = A.nameName n,
                                   A.ndNameType = A.ProcName, A.ndSpecType = newProc, 
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return $ A.Spec m (A.Specification m' n newProc) scope
    -- Functions:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n
      (A.Function m'' funcMode retTypes params funcBody)) scope)
      = do (params', funcBody') <- doFormals params funcBody
           let newFunc = (A.Function m'' funcMode retTypes params' funcBody')
           defineName n A.NameDef {A.ndMeta = m', A.ndName = A.nameName n, A.ndOrigName = A.nameName n,
                                   A.ndNameType = A.FunctionName, A.ndSpecType = newFunc,
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return $ A.Spec m (A.Specification m' n newFunc) scope

    -- replicator names have their types recorded later, but are
    -- uniquified and resolved here
    uniquifyAndResolveVars' (A.Rep m (A.ForEach m' n e) scope)
      = do n' <- makeNonce $ A.nameName n
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return $ A.Rep m (A.ForEach m' (n {A.nameName = n'}) e) scope'
    --Other:
    uniquifyAndResolveVars' s = return s

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
                                         A.ndNameType = A.VariableName, A.ndSpecType = (A.Declaration m t),
                                         A.ndAbbrevMode = am, A.ndPlacement = A.Unplaced}
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return (A.Formal am t newName, scope')

-- | Helper function for a few of the passes.  Replaces 'A.nameName' of a 'A.Name' if it matches a given 'String'.
replaceNameName :: 
  String     -- ^ The variable name to be replaced.
  -> String  -- ^ The new variable to use instead.
  -> A.Name  -- ^ The name to check.
  -> A.Name  -- ^ The new name, with the 'A.nameName' field replaced if it matched.
replaceNameName find replace n = if (A.nameName n) == find then n {A.nameName = replace} else n

-- | A pass that finds and tags the main process, and also mangles its name (to avoid problems in the C\/C++ backends with having a function called main).
findMain :: PassType
--Because findMain runs after uniquifyAndResolveVars, the types of all the process will have been recorded
--Therefore this pass doesn't actually need to walk the tree, it just has to look for a process named "main"
--in the CompState, and pull it out into csMainLocals
findMain x = do newMainName <- makeNonce "main_"
                modify (findMain' newMainName)
                applyDepthM (return . (replaceNameName "main" newMainName)) x
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
transformEachRange :: PassType
transformEachRange = applyDepthSM doStructured
  where
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Rep repMeta (A.ForEach eachMeta loopVar (A.ExprConstr
      _ (A.RangeConstr _ _ begin end))) body)
        =   do -- Need to change the stored abbreviation mode to original:
               modifyName loopVar $ \nd -> nd { A.ndAbbrevMode = A.Original }
               return $ A.Rep repMeta (A.For eachMeta loopVar begin
                 (addOne $ subExprs end begin)) body
    doStructured s = return s

-- | A pass that changes all the Rain range constructor expressions into the more general array constructor expressions
--
-- TODO make sure when the range has a bad order that an empty list is
-- returned
transformRangeRep :: PassType
transformRangeRep = applyDepthM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.ExprConstr _ (A.RangeConstr m t begin end))
          =        do A.Specification _ rep _ <- makeNonceVariable "rep_constr" m A.Int A.VariableName A.ValAbbrev
                      let count = addOne $ subExprs end begin
                      return $ A.ExprConstr m $ A.RepConstr m t
                        (A.For m rep begin count)
                          (A.ExprVariable m $ A.Variable m rep)
    doExpression e = return e

-- TODO this is almost certainly better figured out from the CFG
checkFunction :: PassType
checkFunction = return -- applyDepthM checkFunction'
  where
    checkFunction' :: A.Specification -> PassM A.Specification
    checkFunction' spec@(A.Specification _ n (A.Function m _ _ _ (Right body)))
      = case body of 
          (A.Seq m' seqBody) ->
            let A.Several _ statements = skipSpecs seqBody in
            if (null statements)
              then dieP m "Functions must not have empty bodies"
              else case (last statements) of
                (A.Only _ (A.Assign _ [A.Variable _ dest] _)) -> if A.nameName n == A.nameName dest then return spec else
                  dieP m "Functions must have a return statement as their last statement."
                _ -> dieP m "Functions must have a return statement as their last statement"
          _ -> dieP m $ "Functions must have seq[uential] bodies, found instead: "
                 ++ showConstr (toConstr body)
    checkFunction' s = return s

    skipSpecs :: A.Structured A.Process -> A.Structured A.Process
    skipSpecs (A.Spec _ _ inner) = skipSpecs inner
    skipSpecs s = s

-- | Pulls up the list expression into a variable.
-- This is done no matter how simple the expression is; when we reach the
-- backend we need it to be a variable so we can use begin() and end() (in
-- C++); these will only be valid if exactly the same list is used
-- throughout the loop.
pullUpForEach :: PassType
pullUpForEach = applyDepthSM doStructured
  where
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Rep m (A.ForEach m' loopVar loopExp) s)
     = do (extra, loopExp') <- case loopExp of
            A.ExprVariable {} -> return (id, loopExp)
            _ -> do t <- astTypeOf loopExp
                    spec@(A.Specification _ n _) <- makeNonceIsExpr
                      "loop_expr" m' t loopExp
                    return (A.Spec m' spec, A.ExprVariable m' (A.Variable m' n))
          return $ extra $ A.Rep m (A.ForEach m' loopVar loopExp') s
    doStructured s = return s
      
    
pullUpParDeclarations :: PassType
pullUpParDeclarations = applyDepthM pullUpParDeclarations'
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
   ,con1 A.Port
   ,con2 A.BytesInExpr
   ,con2 A.BytesInType
   ,con3 A.OffsetOf
   ,con0 A.After
   ,con3 A.InCounted
   ,con3 A.OutCounted
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

