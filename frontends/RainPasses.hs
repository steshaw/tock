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
import Metadata
import Pass
import qualified Properties as Prop
import RainTypes
import SimplifyTypes
import Traversal
import TreeUtils
import Types

-- | An ordered list of the Rain-specific passes to be run.
rainPasses :: [Pass A.AST]
rainPasses =
     [ excludeNonRainFeatures
     , rainOnlyPass "Dummy Rain pass" [] [Prop.retypesChecked] return
     , transformInt
     , uniquifyAndResolveVars
     , performTypeUnification
     , constantFoldPass
     ] ++ enablePassesWhen ((== FrontendRain) . csFrontend) simplifyTypes ++
     [ findMain
     , transformEachRange
     , pullUpForEach
     , transformRangeRep
     , pullUpParDeclarations
     , mobiliseLists
     , implicitMobility
     ]

-- | A pass that transforms all instances of 'A.Int' into 'A.Int64'
transformInt :: PassOn A.Type
transformInt = rainOnlyPass "Resolve Int -> Int64" [] [Prop.noInt] (applyBottomUpM transformInt')
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
uniquifyAndResolveVars :: PassOnStruct
uniquifyAndResolveVars = rainOnlyPass
  "Uniquify variable declarations, record declared types and resolve variable names"
  [Prop.noInt] (Prop.agg_namesDone \\ [Prop.inferredTypesRecorded])
  (applyBottomUpMS uniquifyAndResolveVars')
  where
    uniquifyAndResolveVars' :: Data a => A.Structured a -> PassM (A.Structured a)
             
    --Processes:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n (A.Proc m'' procMode params procBody)) scope) 
      = do (params',procBody') <- doFormals params procBody
           let newProc = (A.Proc m'' procMode params' procBody')
           defineName n A.NameDef {A.ndMeta = m', A.ndName = A.nameName n, A.ndOrigName = A.nameName n,
                                   A.ndSpecType = newProc, A.ndNameSource = A.NameUser,
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return $ A.Spec m (A.Specification m' n newProc) scope
    -- Functions:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n
      (A.Function m'' funcMode retTypes params funcBody)) scope)
      = do (params', funcBody') <- doFormals params funcBody
           let newFunc = (A.Function m'' funcMode retTypes params' funcBody')
           defineName n A.NameDef {A.ndMeta = m', A.ndName = A.nameName n, A.ndOrigName = A.nameName n,
                                   A.ndSpecType = newFunc, A.ndNameSource = A.NameUser,
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return $ A.Spec m (A.Specification m' n newFunc) scope

    --Variable declarations and replicators:
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n decl) scope) 
      = do n' <- makeNonce m $ A.nameName n
           defineName (n {A.nameName = n'}) A.NameDef {A.ndMeta = m', A.ndName = n', A.ndOrigName = A.nameName n, 
                                                       A.ndSpecType = decl, A.ndNameSource = A.NameUser,
                                                       A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return $ A.Spec m (A.Specification m' n {A.nameName = n'} decl) scope'

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
      = do n' <- makeNonce (A.nameMeta n) $ A.nameName n
           let newName = (n {A.nameName = n'})
           let m = A.nameMeta n
           defineName newName A.NameDef {A.ndMeta = m, A.ndName = n', A.ndOrigName = A.nameName n, 
                                         A.ndSpecType = (A.Declaration m t),
                                         A.ndNameSource = A.NameUser,
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
findMain :: PassOn A.Name
--Because findMain runs after uniquifyAndResolveVars, the types of all the process will have been recorded
--Therefore this pass doesn't actually need to walk the tree, it just has to look for a process named "main"
--in the CompState, and pull it out into csMainLocals
findMain = rainOnlyPass "Find and tag the main function" Prop.agg_namesDone [Prop.mainTagged]
  (    \x -> do newMainName <- makeNonce emptyMeta "main_"
                modify (findMain' newMainName)
                applyBottomUpM (return . (replaceNameName "main" newMainName)) x)
  where
    --We have to mangle the main name because otherwise it will cause problems on some backends (including C and C++)
    findMain' :: String -> CompState -> CompState
    findMain' newn st = case Map.lookup "main" (csNames st) of
      Just n -> st { csNames = changeMainName newn (csNames st)
                   , csMainLocals = makeMainLocals (findMeta n) newn
                   }
      Nothing -> st

    changeMainName :: String -> Map.Map String A.NameDef -> Map.Map String A.NameDef
    changeMainName newn m = case Map.lookup "main" m of
      Just nd -> Map.insert newn (nd {A.ndName = newn}) $
                   Map.delete "main" m
      Nothing -> m

    -- The Rain parser doesn't set csMainLocals, so this pass constructs it
    -- from scratch.
    makeMainLocals :: Meta -> String -> [(String, (A.Name, NameType))]
    makeMainLocals m newn = [(newn, (A.Name m newn, ProcName))]

checkIntegral :: A.LiteralRepr -> Maybe Integer
checkIntegral (A.IntLiteral _ s) = Just $ read s
checkIntegral (A.HexLiteral _ s) = Nothing -- TODO support hex literals
checkIntegral (A.ByteLiteral _ s) = Nothing -- TODO support char literals
checkIntegral _ = Nothing

-- | Transforms seqeach\/pareach loops over things like [0..99] into SEQ i = 0 FOR 100 loops
transformEachRange :: PassOn A.Specification
transformEachRange = rainOnlyPass "Convert seqeach/pareach loops over ranges into simple replicated SEQ/PAR"
  (Prop.agg_typesDone ++ [Prop.constantsFolded]) [Prop.eachRangeTransformed]
  (applyBottomUpM doSpec)
  where
    doSpec :: A.Specification -> PassM A.Specification
    doSpec
      (A.Specification mspec loopVar
        (A.Rep repMeta             -- Outer replicator
          (A.ForEach eachMeta      -- goes through each itme
            (A.Literal _ _
              (A.RangeLiteral _ begin end) -- a list made from a range
            )
          )
        )
      ) =   do -- Need to change the stored abbreviation mode to original:
               modifyName loopVar $ \nd -> nd { A.ndAbbrevMode = A.Original }
               newCount <- subExprs end begin >>= addOne
               return $ A.Specification mspec loopVar $ A.Rep repMeta $
                 A.For eachMeta begin newCount (makeConstant eachMeta 1)
    doSpec s = return s

-- | A pass that changes all the Rain range constructor expressions into the more general array constructor expressions
--
-- TODO make sure when the range has a bad order that an empty list is
-- returned
transformRangeRep :: Pass
transformRangeRep = rainOnlyPass "Convert simple Rain range constructors into more general array constructors"
  (Prop.agg_typesDone ++ [Prop.eachRangeTransformed])
  [Prop.rangeTransformed]
  (applyDepthM doExpression)
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.ExprConstr _ (A.RangeConstr m t begin end))
          =        do A.Specification _ rep _ <- makeNonceVariable "rep_constr" m A.Int A.ValAbbrev
                      let count = addOne $ subExprs end begin
                      return $ A.ExprConstr m $ A.RepConstr m t rep
                        (A.For m begin count $ makeConstant m 1)
                          (A.ExprVariable m $ A.Variable m rep)
    doExpression e = return e

-- TODO this is almost certainly better figured out from the CFG
{-
checkFunction :: Pass t
checkFunction = return -- applyDepthM checkFunction'
  where
    checkFunction' :: A.Specification -> PassM A.Specification
    checkFunction' spec@(A.Specification _ n (A.Function m _ _ _ (Just (Right body))))
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
-}

-- | Pulls up the list expression into a variable.
-- This is done no matter how simple the expression is; when we reach the
-- backend we need it to be a variable so we can use begin() and end() (in
-- C++); these will only be valid if exactly the same list is used
-- throughout the loop.
pullUpForEach :: PassOnStruct
pullUpForEach = rainOnlyPass "Pull up foreach-expressions"
  (Prop.agg_typesDone ++ [Prop.constantsFolded]) [Prop.eachTransformed]
  (applyBottomUpMS doStructured)
  where
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Spec mstr (A.Specification mspec loopVar (A.Rep m (A.ForEach m' loopExp))) s)
     = do (extra, loopExp') <- case loopExp of
            A.ExprVariable {} -> return (id, loopExp)
            _ -> do t <- astTypeOf loopExp
                    spec@(A.Specification _ n _) <- makeNonceIsExpr
                      "loop_expr" m' t loopExp
                    return (A.Spec m' spec, A.ExprVariable m' (A.Variable m' n))
          return $ extra $ A.Spec mstr (A.Specification mspec loopVar $ A.Rep m $
            A.ForEach m' loopExp') s
    doStructured s = return s
      
    
pullUpParDeclarations :: PassOn A.Process
pullUpParDeclarations = rainOnlyPass "Pull up par declarations"
  [] [Prop.rainParDeclarationsPulledUp]
  (applyBottomUpM pullUpParDeclarations')
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

mobiliseLists :: PassOn A.Type
mobiliseLists = rainOnlyPass "Mobilise lists" [] [] --TODO properties
  (\x -> (get >>= applyBottomUpM mobilise >>= put) >> applyBottomUpM mobilise x)
  where
    mobilise :: A.Type -> PassM A.Type
    mobilise t@(A.List _) = return $ A.Mobile t
    mobilise t = return t

-- | All the items that should not occur in an AST that comes from Rain (up until it goes into the shared passes).
excludeNonRainFeatures :: Pass A.AST
excludeNonRainFeatures = rainOnlyPass "AST Validity check, Rain #1" [] []
  (excludeConstr
  [ con0 A.Real32
   ,con0 A.Real64
   ,con2 A.Counted
   ,con1 A.Port
   ,con2 A.BytesInExpr
   ,con2 A.BytesInType
   ,con3 A.OffsetOf
   ,con3 A.InCounted
   ,con3 A.OutCounted
   ,con2 A.Place
   ,con1 A.ActualChannelArray
   ,con4 A.Retypes
   ,con4 A.RetypesExpr
   ,con0 A.PriPar
   ,con0 A.PlacedPar
   ,con1 A.Stop
   ,con3 A.Processor
   ,con3 A.IntrinsicProcCall
  ])

