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

-- | Passes associated with the backends
module BackendPasses (backendPasses, transformWaitFor, declareSizesArray) where

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import CompState
import Errors
import EvalConstants
import Metadata
import Pass
import PrettyShow
import qualified Properties as Prop
import ShowCode
import Traversal
import Types
import Utils

backendPasses :: [Pass]
backendPasses =
    -- Note that removeDirections is only for C, whereas removeUnneededDirections
    -- is for all backends
  [ removeDirectionsForC
  , removeUnneededDirections
  , simplifySlices
  , declareSizesArray
  , fixMinInt
-- This is not needed unless forking:
--  , mobileReturn
  ]

prereq :: [Property]
prereq = Prop.agg_namesDone ++ Prop.agg_typesDone ++ Prop.agg_functionsGone ++ [Prop.subscriptsPulledUp, Prop.arrayLiteralsExpanded]

-- | Remove all variable directions for the C backend.
-- They're unimportant in occam code once the directions have been checked,
-- and this somewhat simplifies the work of the later passes.
removeDirectionsForC :: Pass
removeDirectionsForC
    = occamAndCOnlyPass "Remove variable directions"
                    prereq
                    [Prop.directionsRemoved]
                    (applyDepthM (return . doVariable))
  where
    doVariable :: A.Variable -> A.Variable
    doVariable (A.DirectedVariable _ _ v) = v
    doVariable v = v

-- | Remove variable directions that are superfluous.  This prevents confusing
-- later passes, where the user has written something like:
-- []CHAN INT da! IS ...:
-- foo(da!)
--
-- The second direction specifier is unneeded, and will confuse passes such as
-- those adding sizes parameters (which looks for plain variables, since directed
-- arrays should already have been pulled up).
removeUnneededDirections :: Pass
removeUnneededDirections
  = occamOnlyPass "Remove unneeded variable directions"
                  prereq
                  []
                  (applyDepthM doVariable)
  where
    doVariable :: Transform (A.Variable)
    doVariable whole@(A.DirectedVariable m dir v)
       = do t <- astTypeOf v
            case t of
              A.Chan {} -> return whole
              A.Array _ (A.Chan {}) -> return whole
              A.ChanEnd chanDir _ _ | dir == chanDir -> return v
              A.Array _ (A.ChanEnd chanDir _ _) | dir == chanDir -> return v
              _ -> diePC m $ formatCode "Direction applied to non-channel type: %" t
    doVariable v = return v

-- | Turns any literals equivalent to a MOSTNEG back into a MOSTNEG
-- The reason for doing this is that C (and presumably C++) don't technically (according
-- to the standard) allow you to write INT_MIN directly as a constant.  GCC certainly
-- warns about it.  So this pass takes any MOSTNEG-equivalent values (that will have been
-- converted to constants in the constant folding earlier) and turns them back
-- into MOSTNEG, for which the C backend uses INT_MIN and similar, which avoid
-- this problem.
fixMinInt :: Pass
fixMinInt
  = cOrCppOnlyPass "Turn any literals that are equal to MOSTNEG INT back into MOSTNEG INT"
                   prereq
                   []
                   (applyDepthM doExpression)
  where
    doExpression :: Transform (A.Expression)
    doExpression l@(A.Literal m t (A.IntLiteral m' s))
      = do folded <- constantFold (A.MostNeg m t)
           case folded of
             (A.Literal _ _ (A.IntLiteral _ s'), _, _)
               -> if (s == s')
                    then return $ A.MostNeg m t
                    else return l
             _ -> return l -- This can happen as some literals retain the Infer
                           -- type which fails the constant folding
    doExpression e = return e

transformWaitFor :: Pass
transformWaitFor = cOnlyPass "Transform wait for guards into wait until guards"
  []
  [Prop.waitForRemoved]
  (applyDepthM doAlt)
  where
    doAlt :: A.Process -> PassM A.Process
    doAlt a@(A.Alt m pri s)
      = do (s',(specs,code)) <- runStateT (transformOnly doWaitFor s) ([],[])
           if (null specs && null code)
             then return a
             else return $ A.Seq m $ foldr addSpec (A.Several m (code ++ [A.Only m $ A.Alt m pri s'])) specs
    doAlt p = return p
    
    addSpec :: Data a => (A.Structured a -> A.Structured a) -> A.Structured a -> A.Structured a
    addSpec spec inner = spec inner

    doWaitFor :: Meta -> A.Alternative -> StateT ([A.Structured A.Process -> A.Structured A.Process], [A.Structured A.Process]) PassM (A.Structured A.Alternative)
    doWaitFor m'' a@(A.Alternative m cond tim (A.InputTimerFor m' e) p)
      = do (specs, init) <- get
           id <- lift $ makeNonce m "waitFor"
           let n = A.Name m id
           let var = A.Variable m n
           put (specs ++ [A.Spec m (A.Specification m n (A.Declaration m A.Time))], 
                init ++ [A.Only m $ A.Input m tim
                           (A.InputTimerRead m (A.InVariable m var)),
                         A.Only m $ A.Assign m [var] $ A.ExpressionList m [A.Dyadic m A.Plus (A.ExprVariable m var) e]])
           return $ A.Only m'' $ A.Alternative m cond tim (A.InputTimerAfter m' (A.ExprVariable m' var)) p
               
    doWaitFor m a = return $ A.Only m a

-- | Declares an array filled with constant sizes
-- If any extra sizes are declared, will add them to the current context
getSizes :: Meta -> [A.Expression] -> PassM A.Name
getSizes m [] = dieP m "Empty list of dimensions in getSizes"
getSizes m es
  = do ces <- mapM evalIntExpression es
       ss <- getCompState >>* csGlobalSizes
       case Map.lookup ces ss of
         Just n -> return $ A.Name m n
         Nothing -> let base = "sizes" ++ concat (intersperse "_" $ map show ces)
                        t = A.Array [A.Dimension $ makeConstant m $ length es] A.Int
                        val = A.ArrayListLiteral m $ A.Several m $
                          map (A.Only m) $ es
                        e = A.Literal m t val
           in do spec@(A.Specification _ n _) <- makeNonceIsExpr base m t e
                 addPulled (m, Left spec)
                 modify $ \cs -> cs { csGlobalSizes = Map.insert ces (A.nameName n) ss }
                 return n

-- Forms a slice that drops a certain amount of elements:
sliceDrop :: Meta -> Int -> Int -> A.Variable -> A.Variable
sliceDrop m skip total
  = A.SubscriptedVariable m (A.SubscriptFromFor m A.NoCheck
      (makeConstant m skip) (makeConstant m (total - skip)))

-- Used by findVarSizes when it can't descend any further:
-- The Variable returned will always be Just, but it makes use from findVarSizes
-- easier
findSizeForVar :: Meta -> Int -> A.Variable ->
  PassM (Maybe A.Name, Maybe A.Variable, [A.Expression])
findSizeForVar m skip v
  = do t <- astTypeOf v
       case t of
         A.Array ds _
           | A.UnknownDimension `notElem` ds
             -> do let es = drop skip [e | A.Dimension e <- ds]
                   n <- getSizes m es
                   return (Just n, Just $ A.Variable m n, es)
           | otherwise
             -> return (Nothing, Just $ sliceDrop m skip (length ds) $ A.VariableSizes m v,
                  [A.ExprVariable m $ A.SubscriptedVariable m (A.Subscript m A.NoCheck $ makeConstant
                    m i) (A.VariableSizes m v)
                  | i <- [skip  .. (length ds - 1)]])
         _ -> diePC m $ formatCode "findSizeForVar for type % (for variable %)" t v

-- Gets the variable that holds the sizes of the given variable.  The first parameter
-- is the number of dimensions to skip.  Assumes simplifySlices has already been
-- run
findVarSizes :: Int -> A.Variable -> PassM (Maybe A.Name, Maybe A.Variable, [A.Expression])
findVarSizes skip v@(A.Variable m _) = findSizeForVar m skip v
findVarSizes skip (A.DirectedVariable _ _ v) = findVarSizes skip v
-- Fields are either constant or need a VariableSizes:
findVarSizes skip v@(A.SubscriptedVariable m (A.SubscriptField {}) _)
  = findSizeForVar m skip v
-- For a specific subscript, drop one extra dimension off the inner dimensions:
findVarSizes skip (A.SubscriptedVariable _ (A.Subscript {}) v)
  = findVarSizes (skip + 1) v
-- This covers all slicing:
findVarSizes skip v@(A.SubscriptedVariable m (A.SubscriptFromFor _ _ from for) innerV)
-- If we are skipping at least one dimension, we can ignore slicing:
  | skip > 0 = findVarSizes skip innerV
  | otherwise = do (_, _, _:es) <- findVarSizes 0 innerV
                   return (Nothing, Nothing, for : es)
-- the size of a dereference is the size of the mobile array:
findVarSizes skip (A.DerefVariable _ v) = findVarSizes skip v
-- Not sure this should ever happen, but no harm:
findVarSizes skip (A.VariableSizes m v)
  = do A.Array ds _ <- astTypeOf v
       let es = drop skip [makeConstant m (length ds)]
       n <- getSizes m es
       return (Just n, Just $ A.Variable m n, es)


-- | Declares a _sizes array for every array, statically sized or dynamically sized.
-- For each record type it declares a _sizes array too.
declareSizesArray :: Pass
declareSizesArray = occamOnlyPass "Declare array-size arrays"
  (prereq ++ [Prop.slicesSimplified, Prop.arrayConstructorsRemoved])
  [Prop.arraySizesDeclared]
  (passOnlyOnAST "declareSizesArray" $
   \t -> do pushPullContext
            t' <- recurse t >>= applyPulled
            popPullContext
            exts <- getCompState >>* csExternals
            exts' <- sequence [do fs' <- transformExternal (findMeta t) extType fs
                                  modifyName (A.Name emptyMeta n) $ \nd -> nd
                                    {A.ndSpecType = A.Proc (findMeta t)
                                      (A.PlainSpec, A.PlainRec) fs' (A.Skip (findMeta t))}
                                  return $ (n, (extType, fs'))
                              | (n, (extType, fs)) <- exts]
            modify $ \cs -> cs { csExternals = exts' }
            return t'
            )
  where
    ops :: OpsM PassM
    ops = baseOp `extOpS` doStructured `extOp` doProcess
    recurse, descend :: Data a => Transform a
    recurse = makeRecurse ops
    descend = makeDescend ops
    
    defineSizesName :: Meta -> A.Name -> A.SpecType -> PassM ()
    defineSizesName m n spec
      = defineName n $ A.NameDef { A.ndMeta = m
                                 , A.ndName = A.nameName n
                                 , A.ndOrigName = A.nameName n
                                 , A.ndSpecType = spec
                                 , A.ndAbbrevMode = A.ValAbbrev
                                 , A.ndNameSource = A.NameNonce
                                 , A.ndPlacement = A.Unplaced
                                 }

    addSizes :: String -> A.Name -> PassM ()
    addSizes k v = modify $ \cs -> cs { csArraySizes = Map.insert k v $ csArraySizes cs }

    -- | Generate the @_sizes@ array for a 'Retypes' expression.
    retypesSizes :: Meta -> A.Name -> [A.Dimension] -> A.Type -> A.Variable
      -> PassM (A.Name, Maybe A.SpecType)
    retypesSizes m n_sizes ds elemT v@(A.Variable _ nSrc)
      =  do biDest <- bytesInType (A.Array ds elemT)
            tSrc <- astTypeOf v
            biSrc <- bytesInType tSrc

            -- Figure out the size of the source.
            srcSize <-
              case (biSrc, tSrc) of
                -- Fixed-size source -- easy.
                (BIJust size, _) -> return size
                -- Variable-size source -- it must be an array, so multiply
                -- together the dimensions.
                (_, A.Array ds t) ->
                    do BIJust elementSize <- bytesInType t
                       return $ foldl mulExprs elementSize dSizes
                  where
                    dSizes = [case d of
                                -- Fixed dimension.
                                A.Dimension e -> e
                                -- Variable dimension -- use the corresponding
                                -- element of its _sizes array.
                                A.UnknownDimension -> A.ExprVariable m $ specificDimSize i v
                              | (d, i) <- zip ds [0..]]
                -- Must be an unpacked record if it's not BIJust:
                (_, A.Record {}) ->
                  return $ A.BytesInType m tSrc
                _ -> dieP m "Cannot compute size of source type"

            -- Build the _sizes array for the destination.
            sizeSpecType <- return $
              case biDest of
                -- Destination size is fixed -- so we must know the dimensions.
                BIJust _ -> makeSizeSpec m [e | A.Dimension e <- ds]
                -- Destination has one free dimension, so we need to compute
                -- it.
                BIOneFree destSize n ->
                  let newDim = A.Dimension $ divExprs srcSize destSize
                      ds' = replaceAt n newDim ds in
                  makeSizeSpec m [e | A.Dimension e <- ds']

            return (n_sizes, Just sizeSpecType)

    varSizes :: Meta -> A.Name -> A.Variable -> PassM (A.Name, Maybe A.SpecType)
    varSizes m n_sizes abbrevV
      = do sizeExpr <- findVarSizes 0 abbrevV
           case sizeExpr of
             -- It was constant, and a new global declaration made, so we just
             -- need to return the name, and no specification
             (Just sizeN, _, _) -> return (sizeN, Nothing)
             -- We can use/slice a previous sizes item, so our abbreviation is
             -- quite simple:
             (Nothing, Just sizeV, _) ->
               do t <- astTypeOf sizeV
                  return (n_sizes, Just $ A.Is m A.ValAbbrev t (A.ActualVariable sizeV))
             -- We have to declare a full array of sizes:
             (Nothing, Nothing, es) -> return (n_sizes, Just $ makeSizeSpec m es)

    makeSizeSpec :: Meta -> [A.Expression] -> A.SpecType
    makeSizeSpec m es = A.Is m A.ValAbbrev t (A.ActualExpression e)
      where
        e = A.Literal m t lit
        lit = A.ArrayListLiteral m $ A.Several m $ map (A.Only m) es
        t = A.Array [A.Dimension $ makeConstant m (length es)] A.Int

    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured str@(A.Spec m sp@(A.Specification m' n spec) s)
      = do t <- typeOfSpec spec
           case (spec, t) of
             (_, Just (A.Array ds elemT)) ->
                  -- nonce_sizes is a suggested name, may not actually be used:
               do nonce_sizes <- makeNonce m (A.nameName n ++ "_sizes") >>* A.Name m
                  let varSize = varSizes m nonce_sizes 
                  (n_sizes, msizeSpec) <-
                      case spec of
                        -- TODO I think retyping a channel array ends up
                        -- here, and probably isn't handled right
                        A.Retypes _ _ _ v -> retypesSizes m' nonce_sizes ds elemT v
                        A.Is _ _ _ (A.ActualVariable v) -> varSize v
                        A.Is _ _ _ (A.ActualExpression (A.ExprVariable _ v)) -> varSize v
                        -- For all other cases, we should be able to figure
                        -- out the size from ourself:
                        _ -> varSize (A.Variable m n)
                  addSizes (A.nameName n) n_sizes
                  maybe (return ()) (defineSizesName m n_sizes) msizeSpec
                  s' <- recurse s
                  return (maybe id (A.Spec m . A.Specification m n_sizes) msizeSpec $ A.Spec m sp s')
             (A.Proc m' sm args body, _) ->
               do -- We descend into the scope first, so that all the actuals get
                  -- fixed before the formals:
                  s' <- recurse s
                  (args', newargs) <- transformFormals Nothing m args
                  sequence_ [defineSizesName m' n (A.Declaration m' t)
                            | A.Formal _ t n <-  newargs]
                  -- We descend into the body after the formals have been
                  -- processed, but before our spec is updated (to avoid
                  -- problems for recursive PROCs with arrays.
                  body' <- recurse body
                  let newspec = A.Proc m' sm args' body'
                  modify (\cs -> cs {csNames = Map.adjust (\nd -> nd { A.ndSpecType = newspec })
                    (A.nameName n) (csNames cs)})
                  return $ A.Spec m (A.Specification m n newspec) s'
             _ -> descend str
    doStructured s = descend s

    transformExternal :: Meta -> ExternalType -> [A.Formal] -> PassM [A.Formal]
    transformExternal m extType args
      = do (args', newargs) <- transformFormals (Just extType) m args
           sequence_ [defineSizesName m n (A.Declaration m t)
                     | A.Formal _ t n <-  newargs]
           return args'

    transformFormals :: Maybe ExternalType -> Meta -> [A.Formal] -> PassM ([A.Formal], [A.Formal])
    transformFormals _ _ [] = return ([],[])
    transformFormals ext m ((f@(A.Formal am t n)):fs)
      = case (t, ext) of
          -- For externals, we always add extra formals (one per dimension!):
          (A.Array ds _, Just ExternalOldStyle) ->
                          do params <- replicateM (length ds) $ makeNonce m "ext_size"
                             let newfs = map (A.Formal A.ValAbbrev A.Int . A.Name m) params
                             (rest, moreNew) <- transformFormals ext m fs
                             return (f : newfs ++ rest, newfs ++ moreNew)

          -- For occam PROCs, only bother adding the extra formal if the dimension
          -- is unknown:
          (A.Array ds _, _)
            | A.UnknownDimension `elem` ds ->
                          do let sizeType = A.Array [makeDimension m $ length ds] A.Int
                             n_sizes <- makeNonce m (A.nameName n ++ "_sizes") >>* A.Name m
                             addSizes (A.nameName n) n_sizes
                             let newf = A.Formal A.ValAbbrev sizeType n_sizes
                             (rest, moreNew) <- transformFormals ext m fs
                             return (f : newf : rest, newf : moreNew)
          -- But even if all the dimensions are known, we must still add the sizes
          -- as a global thingy:
            | otherwise ->
                          do (Just n_sizes, _, _) <- findVarSizes 0 (A.Variable m n)
                             addSizes (A.nameName n) n_sizes
                             (rest, moreNew) <- transformFormals ext m fs
                             return (f : rest, moreNew)
          _ -> do (rest, new) <- transformFormals ext m fs
                  return (f : rest, new)


    doProcess :: A.Process -> PassM A.Process
    doProcess (A.ProcCall m n params)
      = do ext <- getCompState >>* csExternals >>* lookup (A.nameName n) >>* fmap fst
           A.Proc _ _ fs _ <- specTypeOfName n
           concatMapM (transformActual ext) (zip fs params) >>* A.ProcCall m n
    doProcess p = descend p

    transformActual :: Maybe ExternalType -> (A.Formal, A.Actual) -> PassM [A.Actual]
    transformActual ext (A.Formal _ t _, a@(A.ActualVariable v))
      = transformActualVariable ext t a v
    transformActual ext (A.Formal _ t _, a@(A.ActualExpression (A.ExprVariable _ v)))
      = transformActualVariable ext t a v
    transformActual _ (_, a) = return [a]

    transformActualVariable :: Maybe ExternalType -> A.Type -> A.Actual -> A.Variable -> PassM [A.Actual]
    transformActualVariable ext t a v
      =    case (t, ext) of
             (A.Array ds _, Just ExternalOldStyle) ->
                let acts = map (sub $ A.VariableSizes m v) [0 .. (length ds - 1)]
                in return $ a : acts
             -- Note that t is the formal type, not the type of the actual
             (A.Array ds _, _) | A.UnknownDimension `elem` ds ->
                do sizeV <- sizes v
                   return [a, A.ActualVariable sizeV]
             _ -> return [a]
      where
        sizes v@(A.Variable m n)
          = do ss <- getCompState >>* csArraySizes
               case Map.lookup (A.nameName n) ss of
                 Just n_sizes -> return $ A.Variable m n_sizes
                 Nothing -> return $ A.VariableSizes m v
        sizes (A.DerefVariable _ v) = sizes v

        m = findMeta v

        sub v n = A.ActualVariable $ A.SubscriptedVariable m
          (A.Subscript m A.NoCheck $ makeConstant m n)
          v

-- | Transforms all slices into the FromFor form.
simplifySlices :: Pass
simplifySlices = occamOnlyPass "Simplify array slices"
  prereq
  [Prop.slicesSimplified]
  (applyDepthM doVariable)
  where
    doVariable :: A.Variable -> PassM A.Variable
    doVariable (A.SubscriptedVariable m (A.SubscriptFor m' check for) v)
      = return (A.SubscriptedVariable m (A.SubscriptFromFor m' check (makeConstant m' 0) for) v)
    doVariable (A.SubscriptedVariable m (A.SubscriptFrom m' check from) v)
      = do A.Array (d:_) _ <- astTypeOf v
           limit <- case d of
             A.Dimension n -> return n
             A.UnknownDimension -> return $ A.ExprVariable m $ specificDimSize 0 v
           return (A.SubscriptedVariable m (A.SubscriptFromFor m' check from (A.Dyadic m A.Subtr limit from)) v)
    doVariable v = return v

-- | Finds all processes that have a MOBILE parameter passed in Abbrev mode, and
-- add the communication back at the end of the process.
mobileReturn :: Pass
mobileReturn = cOnlyPass "Add MOBILE returns" [] [] recurse
  where
    ops = baseOp `extOpS` doStructured `extOp` doProcess

    descend, recurse :: Data a => Transform a
    descend = makeDescend ops
    recurse = makeRecurse ops

    ignoreProc :: A.Name -> PassM Bool
    ignoreProc n
      = do nd <- lookupName n
           return $ "copy_" `isPrefixOf` A.ndOrigName nd -- Bit of a hard-hack

    doProcess :: Transform A.Process
    doProcess (A.ProcCall m n as)
      = do sp <- specTypeOfName n
           fs <- case sp of
             A.Proc _ _ fs _ -> return fs
             _ -> dieP m "PROC with unknown spec-type"
           ig <- ignoreProc n
           if ig
             then return $ A.ProcCall m n as
             else do (surr, as') <- addChansAct m $ zip fs as
                     return $ surr $ A.ProcCall m n as'
    doProcess p = descend p

    chanT t = A.Chan (A.ChanAttributes A.Unshared A.Unshared) t

    addChansAct :: Meta -> [(A.Formal, A.Actual)] -> PassM (A.Process -> A.Process, [A.Actual])
    addChansAct _ [] = return (id, [])
    addChansAct m ((A.Formal am t n, a):fas)
      = do isMobile <- isMobileType t
           (recF, recAS) <- addChansAct m fas
           case (am, isMobile) of
             (A.Abbrev, True)
               -> do sp@(A.Specification _ c _) <- defineNonce m (A.nameName n)
                       (A.Declaration m $ chanT t) A.Original
                     let av = getV a
                     return (\p -> A.Seq m $ A.Spec m sp $ A.Several m
                               [A.Only m (recF p)
                               ,A.Only m $ A.Input m (A.Variable m c) $
                                 A.InputSimple m [A.InVariable m av]]
                            , a : A.ActualVariable (A.Variable m c) : recAS)
             _ -> return (recF, a : recAS)

    getV (A.ActualVariable v) = v
    getV (A.ActualExpression (A.ExprVariable _ v)) = v

    addChansForm :: Meta -> [A.Formal] -> PassM ([A.Process], [A.Formal])
    addChansForm _ [] = return ([], [])
    addChansForm m (f@(A.Formal am t n):fs)
      = do (ps, fs') <- addChansForm m fs
           isMobile <- isMobileType t
           case (am, isMobile) of
             (A.Abbrev, True)
               -> do A.Specification _ c _ <- defineNonce m (A.nameName n)
                       (A.Declaration m $ chanT t) A.Abbrev
                     modifyName n $ \nd -> nd {A.ndAbbrevMode = A.Original}
                     return ( ps ++ [A.Output m (A.Variable m c)
                                      [A.OutExpression m
                                         $ A.ExprVariable m $ A.Variable m n]]
                            , A.Formal A.Original t n : A.Formal A.Abbrev (chanT t) c : fs')
             _ -> return (ps, f : fs')

    doStructured :: Data a => Transform (A.Structured a)
    doStructured s@(A.Spec msp (A.Specification m n (A.Proc m' sm fs pr)) scope)
      = do pr' <- recurse pr
           -- We do the scope first, so that all the callers are updated before
           -- we fix our state:
           scope' <- recurse scope
           ig <- ignoreProc n
           if ig
             then return $ A.Spec msp (A.Specification m n (A.Proc m' sm fs pr')) scope'
             else do (ps, fs') <- addChansForm m fs
                     let newSpec = A.Proc m' sm fs' (A.Seq m' $ A.Several m' $
                                            map (A.Only m') $ pr' : ps)
                     modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                     return $ A.Spec msp (A.Specification m n newSpec) scope'
    doStructured s = descend s
