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

import Control.Monad.Error
import Control.Monad.State
import Data.Generics (Data)
import Data.Generics.Polyplate
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

backendPasses :: [Pass A.AST]
backendPasses =
    -- Note that removeDirections is only for C, whereas removeUnneededDirections
    -- is for all backends
  [ removeDirectionsForC
  , removeUnneededDirections
  , simplifySlices
  , declareSizesArray
  , fixMinInt
  , pullAllocMobile
  , fixMobileForkParams
-- This is not needed unless forking:
--  , mobileReturn
  ]

prereq :: [Property]
prereq = Prop.agg_namesDone ++ Prop.agg_typesDone ++ Prop.agg_functionsGone ++ [Prop.subscriptsPulledUp, Prop.arrayLiteralsExpanded]

-- | Remove all variable directions for the C backend.
-- They're unimportant in occam code once the directions have been checked,
-- and this somewhat simplifies the work of the later passes.
removeDirectionsForC :: PassOn A.Variable
removeDirectionsForC
    = occamAndCOnlyPass "Remove variable directions"
                    prereq
                    [Prop.directionsRemoved]
                    (applyBottomUpM (return . doVariable))
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
removeUnneededDirections :: PassOn A.Variable
removeUnneededDirections
  = occamOnlyPass "Remove unneeded variable directions"
                  prereq
                  []
                  (applyBottomUpM doVariable)
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

type AllocMobileOps = ExtOpMSP BaseOp `ExtOpMP` A.Process

-- | Pulls up any initialisers for mobile allocations.  I think, after all the
-- other passes have run, the only place these initialisers should be left is in
-- assignments (and maybe not even those?) and A.Is items.
pullAllocMobile :: PassOnOps AllocMobileOps
pullAllocMobile = cOnlyPass "Pull up mobile initialisers" [] [] recurse
  where
    ops :: AllocMobileOps
    ops = baseOp `extOpMS` (ops, doStructured) `extOpM` doProcess

    recurse :: RecurseM PassM AllocMobileOps
    recurse = makeRecurseM ops
    descend :: DescendM PassM AllocMobileOps
    descend = makeDescendM ops
    
    doProcess :: Transform A.Process
    doProcess (A.Assign m [v] (A.ExpressionList me [A.AllocMobile ma t (Just e)]))
      = do t' <- calculateType t e
           return $ A.Seq m $ A.Several m $ map (A.Only m) $
             [A.Assign m [v] $ A.ExpressionList me [A.AllocMobile ma t' Nothing]
             ,A.Assign m [A.DerefVariable m v] $ A.ExpressionList me [e]
             ]
    doProcess p = descend p

    doStructured :: TransformStructured' AllocMobileOps
    doStructured (A.Spec mspec (A.Specification mif n
      (A.Is mis am t (A.ActualExpression (A.AllocMobile ma tm (Just e)))))
        body)
      = do body' <- recurse body
           t' <- calculateType t e
           return $ A.Spec mspec (A.Specification mif n $
             A.Is mis am t' $ A.ActualExpression $ A.AllocMobile ma t' Nothing)
             $ A.ProcThen ma
                 (A.Assign ma [A.DerefVariable mif $ A.Variable mif n] $ A.ExpressionList ma [e])
                 body'
    doStructured s = descend s

    -- The Mobile wrapper is on before and after
    calculateType :: A.Type -> A.Expression -> PassM A.Type
    calculateType (A.Mobile (A.Array ds t)) (A.ExprVariable m v)
      = return $ A.Mobile (A.Array ds' t)
        where
          ds' = [case d of
                   A.Dimension {} -> d
                   A.UnknownDimension
                     -> A.Dimension $ A.ExprVariable m $ specificDimSize i v
                | (i, d) <- zip [0..] ds]
    calculateType (A.Mobile (A.Array ds t)) e
      = diePC (findMeta e) $ formatCode "Cannot work out array dimensions from expression %" e
    calculateType t@(A.Mobile _) _ = return t
    calculateType t e = diePC (findMeta e) $ formatCode "Cannot allocate mobile of non-mobile type %" t

-- | Turns any literals equivalent to a MOSTNEG back into a MOSTNEG
-- The reason for doing this is that C (and presumably C++) don't technically (according
-- to the standard) allow you to write INT_MIN directly as a constant.  GCC certainly
-- warns about it.  So this pass takes any MOSTNEG-equivalent values (that will have been
-- converted to constants in the constant folding earlier) and turns them back
-- into MOSTNEG, for which the C backend uses INT_MIN and similar, which avoid
-- this problem.
fixMinInt :: PassOn A.Expression
fixMinInt
  = cOrCppOnlyPass "Turn any literals that are equal to MOSTNEG INT back into MOSTNEG INT"
                   prereq
                   []
                   (applyBottomUpM doExpression)
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

transformWaitFor :: PassOn A.Process
transformWaitFor = cOnlyPass "Transform wait for guards into wait until guards"
  []
  [Prop.waitForRemoved]
  (applyBottomUpM doAlt)
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
                         A.Only m $ A.Assign m [var] $ A.ExpressionList m
                           [dyadicExprInt "PLUS" (A.ExprVariable m var) e]])
           return $ A.Only m'' $ A.Alternative m cond tim (A.InputTimerAfter m' (A.ExprVariable m' var)) p
               
    doWaitFor m a = return $ A.Only m a

type SizesM = StateT (Map.Map [Int] String) PassM

-- | Declares an array filled with constant sizes
-- If any extra sizes are declared, will add them to the current state, which records
-- a map of constant sizes arrays declared for that size.
getSizes :: Meta -> A.Variable -> [A.Expression] -> SizesM (Maybe A.Name)
getSizes m v [] = diePC m $ formatCode "Empty list of dimensions in getSizes for %" v
getSizes m _ es
  = do eces <- sequence [(evalIntExpression e >>* Right)
                           `catchError` (return . Left)
                        | e <- es]
       case splitEither eces of
         (_:_, _) -> return Nothing
         ([], ces) -> do
           ss <- get
           case Map.lookup ces ss of
             Just n -> return $ Just $ A.Name m n
             Nothing ->
                    let base = "sizes" ++ concat (intersperse "_" $ map show ces)
                        t = A.Array [A.Dimension $ makeConstant m $ length es] A.Int
                        val = A.ArrayListLiteral m $ A.Several m $
                          map (A.Only m) $ map (makeConstant m) ces
                        e = A.Literal m t val in do
                 spec@(A.Specification _ n _) <- makeNonceIsExpr base m t e
                 addPulled (m, Left spec)
                 modify $ Map.insert ces (A.nameName n)
                 return $ Just n

-- Forms a slice that drops a certain amount of elements:
sliceDrop :: Meta -> Int -> Int -> A.Variable -> A.Variable
sliceDrop m skip total
  = A.SubscriptedVariable m (A.SubscriptFromFor m A.NoCheck
      (makeConstant m skip) (makeConstant m (total - skip)))

-- Used by findVarSizes when it can't descend any further:
-- The Variable returned will always be Just, but it makes use from findVarSizes
-- easier
findSizeForVar :: Meta -> Int -> A.Variable ->
  SizesM (Maybe (Maybe A.Name, Maybe A.Variable, [A.Expression]))
findSizeForVar m skip v
  = do t <- astTypeOf v
       case stripMobile t of
         A.Array ds _
           | skip >= length ds ->
              -- This can happen, for example, with a mobile array of mobile arrays.
              --  In this case, we need to indicate to our caller that they must
              -- the specific subscript (that they probably skipped over) to find
              -- the size of that mobile array
              return Nothing
           | otherwise ->
              do debug $ show (m, skip, ds)
                 let es = drop skip [e | A.Dimension e <- ds]
                 mn <- case partition (== A.UnknownDimension) ds of
                         ([], ds) -> getSizes m v es
                         _ -> return Nothing
                 case mn of
                   Just n -> return $ Just (Just n, Just $ A.Variable m n, es)
                   _ -> return $ Just (Nothing,
                          Just $ sliceDrop m skip (length ds) $ A.VariableSizes m v,
                          [A.ExprVariable m $ A.SubscriptedVariable m
                             (A.Subscript m A.NoCheck $ makeConstant m i)
                               (A.VariableSizes m v)
                          | i <- [skip  .. (length ds - 1)]])
         _ -> return Nothing
  where
    stripMobile (A.Mobile t) = stripMobile t
{-
    stripMobile (A.Array ds t) = case stripMobile t of
      A.Array ds' innerT -> A.Array (ds ++ ds') innerT
      t' -> A.Array ds t'
-}
    stripMobile t = t
-- Gets the variable that holds the sizes of the given variable.  The first parameter
-- is the number of dimensions to skip.  Assumes simplifySlices has already been
-- run
findVarSizes :: Int -> A.Variable -> SizesM (Maybe (Maybe A.Name, Maybe A.Variable, [A.Expression]))
findVarSizes skip v@(A.Variable m _) = findSizeForVar m skip v
findVarSizes skip (A.DirectedVariable _ _ v) = findVarSizes skip v
-- Fields are either constant or need a VariableSizes:
findVarSizes skip v@(A.SubscriptedVariable m (A.SubscriptField {}) _)
  = findSizeForVar m skip v
-- For a specific subscript, drop one extra dimension off the inner dimensions:
findVarSizes skip wholeV@(A.SubscriptedVariable m (A.Subscript {}) v)
  = do sizes <- findVarSizes (skip + 1) v
       if isJust sizes
         then return sizes
         -- We went too far, and we may be an array of arrays, so try a different
         -- approach:
         else findSizeForVar m skip wholeV
-- This covers all slicing:
findVarSizes skip v@(A.SubscriptedVariable m (A.SubscriptFromFor _ _ from for) innerV)
-- If we are skipping at least one dimension, we can ignore slicing:
  | skip > 0 = findVarSizes skip innerV
  | otherwise = do sizes <- findVarSizes 0 innerV
                   case sizes of
                     Just (_, _, _:es) -> return $ Just (Nothing, Nothing, for : es)
                     _ -> diePC m $ formatCode "Empty sizes for sliced array: %" innerV
-- the size of a dereference is the size of the mobile array:
findVarSizes skip (A.DerefVariable _ v) = findVarSizes skip v
-- Not sure this should ever happen, but no harm:
findVarSizes skip (A.VariableSizes m v)
  = do A.Array ds _ <- astTypeOf v
       when (skip > 0) $
         dieP m "Told to drop (at least) one from size of VariableSizes!"
       let es = drop skip [makeConstant m (length ds)]
       mn <- getSizes m (A.VariableSizes m v) es
       return $ Just (mn, fmap (A.Variable m) mn, es)

type DeclSizeOps = ExtOpM SizesM (ExtOpMS SizesM BaseOp) A.Process

-- | Declares a _sizes array for every array, statically sized or dynamically sized.
-- For each record type it declares a _sizes array too.
declareSizesArray :: Pass A.AST
declareSizesArray = occamOnlyPass "Declare array-size arrays"
  (prereq ++ [Prop.slicesSimplified, Prop.arrayConstructorsRemoved])
  [Prop.arraySizesDeclared]
  (passOnlyOnAST "declareSizesArray"
  (\t -> do pushPullContext
            t' <- evalStateT (recurse t) Map.empty >>= applyPulled
            popPullContext
            return t'
            ))
  where
    ops :: DeclSizeOps
    ops = baseOp `extOpMS` (ops, doStructured) `extOpM` doProcess

    recurse :: RecurseM SizesM DeclSizeOps
    recurse = makeRecurseM ops
    descend :: DescendM SizesM DeclSizeOps
    descend = makeDescendM ops
    
    defineSizesName :: CSM m => Meta -> A.Name -> A.SpecType -> m ()
    defineSizesName m n spec
      = defineName n $ A.NameDef { A.ndMeta = m
                                 , A.ndName = A.nameName n
                                 , A.ndOrigName = A.nameName n
                                 , A.ndSpecType = spec
                                 , A.ndAbbrevMode = A.ValAbbrev
                                 , A.ndNameSource = A.NameNonce
                                 , A.ndPlacement = A.Unplaced
                                 }

    addSizes :: CSM m => String -> A.Name -> m ()
    addSizes k v = modifyCompState $ \cs -> cs { csArraySizes = Map.insert k v $ csArraySizes cs }

    -- | Generate the @_sizes@ array for a 'Retypes' expression.
    retypesSizes :: Meta -> A.Name -> [A.Dimension] -> A.Type -> A.Variable
      -> SizesM (A.Name, Maybe A.SpecType)
    retypesSizes m n_sizes ds elemT v
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
                       return $ foldl mulExprsInt elementSize dSizes
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
                  let newDim = A.Dimension $ divExprsInt srcSize destSize
                      ds' = replaceAt n newDim ds in
                  makeSizeSpec m [e | A.Dimension e <- ds']

            return (n_sizes, Just sizeSpecType)

    varSizes :: Meta -> A.Name -> A.Variable -> SizesM (A.Name, Maybe A.SpecType)
    varSizes m n_sizes abbrevV
      = do sizeExpr <- findVarSizes 0 abbrevV
           case sizeExpr of
             -- It was constant, and a new global declaration made, so we just
             -- need to return the name, and no specification
             Just (Just sizeN, _, _) -> return (sizeN, Nothing)
             -- We can use/slice a previous sizes item, so our abbreviation is
             -- quite simple:
             Just (Nothing, Just sizeV, _) ->
               do t <- astTypeOf sizeV
                  return (n_sizes, Just $ A.Is m A.ValAbbrev t (A.ActualVariable sizeV))
             -- We have to declare a full array of sizes:
             Just (Nothing, Nothing, es) -> return (n_sizes, Just $ makeSizeSpec m es)
             -- Error:
             Nothing -> diePC m $ formatCode "Cannot work out sizes for %" abbrevV

    makeSizeSpec :: Meta -> [A.Expression] -> A.SpecType
    makeSizeSpec m es = A.Is m A.ValAbbrev t (A.ActualExpression e)
      where
        e = A.Literal m t lit
        lit = A.ArrayListLiteral m $ A.Several m $ map (A.Only m) es
        t = A.Array [A.Dimension $ makeConstant m (length es)] A.Int

    doStructured :: (Data a, PolyplateM (A.Structured a) DeclSizeOps () SizesM
                           , PolyplateM (A.Structured a) () DeclSizeOps SizesM)
                    => (A.Structured a) -> SizesM (A.Structured a)
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
                  ext <- getCompState >>* csExternals >>* lookup (A.nameName n)
                  (args', newargs) <- transformFormals ext m args
                  sequence_ [defineSizesName m' n (A.Declaration m' t)
                            | A.Formal _ t n <-  newargs]
                  -- We descend into the body after the formals have been
                  -- processed, but before our spec is updated (to avoid
                  -- problems for recursive PROCs with arrays.
                  body' <- recurse body
                  let newspec = A.Proc m' sm args' body'
                  modifyCompState (\cs -> cs {csNames = Map.adjust (\nd -> nd { A.ndSpecType = newspec })
                    (A.nameName n) (csNames cs)})
                  return $ A.Spec m (A.Specification m n newspec) s'
             _ -> descend str
    doStructured s = descend s
    
    transformFormals :: Maybe ExternalType -> Meta -> [A.Formal] -> SizesM ([A.Formal], [A.Formal])
    transformFormals _ _ [] = return ([],[])
    transformFormals ext m ((f@(A.Formal am t n)):fs)
      = case (t, ext) of
          -- For externals, we always add extra formals (one per dimension!):
          (A.Array ds _, Just ExternalOldStyle) ->
                          do params <- replicateM (length ds) $ makeNonce m "ext_size"
                             let newfs = map (A.Formal A.ValAbbrev A.Int . A.Name m) params
                             (rest, moreNew) <- transformFormals ext m fs
                             return (f : newfs ++ rest, newfs ++ moreNew)
          -- For externals, we always add extra formals (one per dimension!), even
          -- for mobile arrays:
          (A.Mobile (A.Array ds _), Just ExternalOldStyle) ->
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
          -- as a global thingy (provided it's not an external):
            | isNothing ext ->
                          do Just (Just n_sizes, _, _) <- findVarSizes 0 (A.Variable m n)
                             addSizes (A.nameName n) n_sizes
                             (rest, moreNew) <- transformFormals ext m fs
                             return (f : rest, moreNew)
          _ -> do (rest, new) <- transformFormals ext m fs
                  return (f : rest, new)

    doProcess :: A.Process -> SizesM A.Process
    doProcess (A.ProcCall m n params)
      = do ext <- getCompState >>* csExternals >>* lookup (A.nameName n)
           A.Proc _ _ fs _ <- specTypeOfName n
           concatMapM (transformActual ext) (zip fs params) >>* A.ProcCall m n
    doProcess p = descend p

    transformActual :: Maybe ExternalType -> (A.Formal, A.Actual) -> SizesM [A.Actual]
    transformActual ext (A.Formal _ t _, a@(A.ActualVariable v))
      = transformActualVariable ext t a v
    transformActual ext (A.Formal _ t _, a@(A.ActualExpression (A.ExprVariable _ v)))
      = transformActualVariable ext t a v
    transformActual _ (_, a) = return [a]

    transformActualVariable :: Maybe ExternalType -> A.Type -> A.Actual -> A.Variable -> SizesM [A.Actual]
    transformActualVariable ext t a v
      =    case (t, ext) of
             (A.Array ds _, Just ExternalOldStyle) ->
                let acts = map (sub $ A.VariableSizes m v) [0 .. (length ds - 1)]
                in return $ a : acts
             (A.Mobile (A.Array ds _), Just ExternalOldStyle) ->
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
simplifySlices :: PassOn A.Variable
simplifySlices = occamOnlyPass "Simplify array slices"
  prereq
  [Prop.slicesSimplified]
  (applyBottomUpM doVariable)
  where
    doVariable :: A.Variable -> PassM A.Variable
    doVariable (A.SubscriptedVariable m (A.SubscriptFor m' check for) v)
      = return (A.SubscriptedVariable m (A.SubscriptFromFor m' check (makeConstant m' 0) for) v)
    doVariable (A.SubscriptedVariable m (A.SubscriptFrom m' check from) v)
      = do A.Array (d:_) _ <- astTypeOf v
           limit <- case d of
             A.Dimension n -> return n
             A.UnknownDimension -> return $ A.ExprVariable m $ specificDimSize 0 v
           return (A.SubscriptedVariable m (A.SubscriptFromFor m' check from (subExprsInt limit from)) v)
    doVariable v = return v

-- | In occam-pi, parameters passed to FORKed processes have a communication semantics.
--  This particularly affects MOBILE parameters.  The FORKed process will have
-- a MOBILE FOO parameter (or channel bundle, or some other MOBILE type) which
-- will be A.Abbrev, which usually means passing an mt_cb_t**.  But since the FORKed
-- process will outlast the scope in which it is called, we can't actually pass
-- it an mt_cb_t**.  But the FORKed process also might be called normally in
-- sequential code with something of type mt_cb_t**, so we can't alter the definition
-- of the process.
--
-- The solution is to instead alter the definition of the /wrapper/ PROC that wraps
-- the FORKed call.  The wrapper process will receive an mt_cb_t*, and will take
-- the address of the variable when passing it to the /wrapped/ PROC, thus giving
-- it a valid mt_cb_t**.
--
-- The way we do this is to simply change the AbbrevMode on the wrapper PROC from
-- A.Abbrev to A.Original, which will have the right effect in the C backend.
fixMobileForkParams :: PassOn A.Specification
fixMobileForkParams = cOnlyPass "Fix abbreviation modes of MOBILE params to FORKed processes"
  [] [] (applyBottomUpM doSpecification)
  where
    doSpecification :: Transform A.Specification
    doSpecification spec@(A.Specification m n (A.Proc m' smrm fs mbody))
      = do cs <- getCompState
           case Map.lookup n (csParProcs cs) of
             Just ForkWrapper ->
               do fs' <- mapM processFormal fs
                  let specType' = A.Proc m' smrm fs' mbody
                  modifyName n $ \nd -> nd { A.ndSpecType = specType' }
                  return $ A.Specification m n specType'
             _ -> return spec
    doSpecification spec = return spec

    processFormal :: Transform A.Formal
    processFormal f@(A.Formal am t n)
      = do mob <- isMobileType t
           if mob
             then do modifyName n $ \nd -> nd { A.ndAbbrevMode = A.Original }
                     return $ A.Formal A.Original t n
             else return f

-- | Finds all processes that have a MOBILE parameter passed in Abbrev mode, and
-- add the communication back at the end of the process.
{-
mobileReturn :: PassOnOps (ExtOpMSP BaseOp `ExtOpMP` A.Process)
mobileReturn = cOnlyPass "Add MOBILE returns" [] [] recurse
  where
    ops = baseOp `extOpMS` doStructured `extOpM` doProcess

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
    doStructured s@(A.Spec msp (A.Specification m n (A.Proc m' sm fs (Just pr))) scope)
      = do pr' <- recurse pr
           -- We do the scope first, so that all the callers are updated before
           -- we fix our state:
           scope' <- recurse scope
           ig <- ignoreProc n
           if ig
             then return $ A.Spec msp (A.Specification m n (A.Proc m' sm fs $ Just pr')) scope'
             else do (ps, fs') <- addChansForm m fs
                     let newSpec = A.Proc m' sm fs' $ Just (A.Seq m' $ A.Several m' $
                                            map (A.Only m') $ pr' : ps)
                     modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                     return $ A.Spec msp (A.Specification m n newSpec) scope'
    doStructured s = descend s
-}
