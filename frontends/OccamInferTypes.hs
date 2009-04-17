{-
Tock: a compiler for parallel languages
Copyright (C) 2008, 2009  University of Kent

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

-- | The occam typechecker.
module OccamInferTypes (inferTypes, addDirections) where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Generics (Data)
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.Traversable as T

import qualified AST as A
import CompState
import Errors
import Intrinsics
import Metadata
import OccamCheckTypes
import Pass
import qualified Properties as Prop
import ShowCode
import Traversal
import Types
import Utils

-- | Pick the more specific of a pair of types.
betterType :: A.Type -> A.Type -> A.Type
betterType A.Infer t = t
betterType t A.Infer = t
betterType t@(A.UserDataType _) _ = t
betterType _ t@(A.UserDataType _) = t
betterType t1@(A.Array ds1 et1) t2@(A.Array ds2 et2)
  | length ds1 == length ds2
     = A.Array (zipWith betterDim ds1 ds2) $ betterType et1 et2
  | length ds1 < length ds2  = t1
  where
    betterDim A.UnknownDimension d@(A.Dimension _) = d
    -- All other cases (both unknown, right is unknown, both known), use left:
    betterDim d _ = d
betterType t _ = t

--}}}
--{{{  type context management

-- | Run an operation in a given type context.
inTypeContext :: Maybe A.Type -> InferTypeM a -> InferTypeM a
inTypeContext ctx body
    =  do pushTypeContext (case ctx of
                             Just A.Infer -> Nothing
                             _ -> ctx)
          v <- body
          popTypeContext
          return v

-- | Run an operation in the type context 'Nothing'.
noTypeContext :: InferTypeM a -> InferTypeM a
noTypeContext = inTypeContext Nothing

-- | Run an operation in the type context that results from subscripting
-- the current type context.
-- If the current type context is 'Nothing', the resulting one will be too.
inSubscriptedContext :: Meta -> InferTypeM a -> InferTypeM a
inSubscriptedContext m body
    =  do ctx <- getTypeContext
          subCtx <- case ctx of
                      Just t@(A.Array _ _) ->
                        trivialSubscriptType m t >>* Just
                      Just t -> diePC m $ formatCode "Attempting to subscript non-array type %" t
                      Nothing -> return Nothing
          inTypeContext subCtx body

--}}}

addDirections :: PassOn2 A.Process A.Alternative
addDirections = occamOnlyPass "Add direction specifiers to inputs and outputs"
  [] []
  (applyBottomUpM2 doProcess doAlternative)
  where
    doProcess :: Transform A.Process
    doProcess (A.Output m v os)
      = do v' <- makeEnd m A.DirOutput v
           return $ A.Output m v' os
    doProcess (A.OutputCase m v n os)
      = do v' <- makeEnd m A.DirOutput v
           return $ A.OutputCase m v' n os
    doProcess (A.Input m v im@(A.InputSimple {}))
      = do v' <- makeEnd m A.DirInput v
           return $ A.Input m v' im
    doProcess (A.Input m v im@(A.InputCase {}))
      = do v' <- makeEnd m A.DirInput v
           return $ A.Input m v' im
    doProcess p = return p

    doAlternative :: Transform A.Alternative
    doAlternative (A.Alternative m pre v im p)
      = do v' <- case im of
                   A.InputSimple {} -> makeEnd m A.DirInput v
                   A.InputCase {} -> makeEnd m A.DirInput v
                   _ -> return v
           return $ A.Alternative m pre v' im p
    doAlternative a = return a

makeEnd :: Meta -> A.Direction -> Transform A.Variable
makeEnd m dir v
  = case v of
      A.SubscriptedVariable _ _ innerV
        -> do t <- astTypeOf innerV
              case t of
                A.ChanDataType {} -> return v
                _ -> makeEnd'
      _ -> makeEnd'
  where
    makeEnd' :: PassM A.Variable
    makeEnd'
      = do t <- astTypeOf v
           case t of
             A.ChanEnd {} -> return v
             A.Chan {} -> return $ A.DirectedVariable m dir v
             A.Array _ (A.ChanEnd {}) -> return v
             A.Array _ (A.Chan {}) -> return $ A.DirectedVariable m dir v
             -- If unsure (e.g. Infer), just shove a direction on it to be sure:
             _ -> return $ A.DirectedVariable m dir v       

scrubMobile :: InferTypeM a -> InferTypeM a
scrubMobile m
  = do ctx <- getTypeContext
       case ctx of
         (Just (A.Mobile t)) -> inTypeContext (Just t) m
         _ -> m

inferAllocMobile :: Meta -> A.Type -> Infer A.Expression
inferAllocMobile m (A.Mobile {}) e
  = do t <- astTypeOf e >>= underlyingType m
       case t of
         A.Mobile {} -> return e
         _ -> return $ A.AllocMobile m (A.Mobile t) (Just e)
inferAllocMobile _ _ e = return e

data InferTypeState = InferTypeState
  -- The string is the operator, the name is the munged function name, the single
  -- type is the return type
  { csOperators :: [(String, A.Name, A.Type, [A.Type])]
  , csTypeContext :: [Maybe A.Type]
  }

type InferTypeM = StateT InferTypeState PassM

type ExtOpMI ops t = ExtOpM InferTypeM ops t

--{{{  type contexts

-- | Enter a type context.
pushTypeContext :: Maybe A.Type -> InferTypeM ()
pushTypeContext t
    = modify (\ps -> ps { csTypeContext = t : csTypeContext ps })

-- | Leave a type context.
popTypeContext :: InferTypeM ()
popTypeContext
    = modify (\ps -> ps { csTypeContext = tail $ csTypeContext ps })

-- | Get the current type context, if there is one.
getTypeContext :: InferTypeM (Maybe A.Type)
getTypeContext
    =  do ps <- get
          case csTypeContext ps of
            (Just c):_ -> return $ Just c
            _ -> return Nothing

--}}}


--{{{  inferTypes

-- I can't put this in the where clause of inferTypes, so it has to be out
-- here.  It should be the type of ops inside the inferTypes function below.
type InferTypeOps
  = ExtOpMS InferTypeM BaseOp
    `ExtOpMI` A.Expression
    `ExtOpMI` A.Dimension
    `ExtOpMI` A.Subscript
    `ExtOpMI` A.Replicator
    `ExtOpMI` A.Alternative
    `ExtOpMI` A.Process
    `ExtOpMI` A.Variable
    `ExtOpMI` A.Variant

type Infer a = a -> InferTypeM a

-- | Infer types.
inferTypes :: Pass A.AST
inferTypes = occamOnlyPass "Infer types"
  []
  [Prop.inferredTypesRecorded]
  (flip evalStateT (InferTypeState [] []) . recurse)
  where
    ops :: InferTypeOps
    ops = baseOp
          `extOpMS` (ops, doStructured)
          `extOpM` doExpression
          `extOpM` doDimension
          `extOpM` doSubscript
          `extOpM` doReplicator
          `extOpM` doAlternative
          `extOpM` doProcess
          `extOpM` doVariable
          `extOpM` doVariant

    recurse :: RecurseM InferTypeM InferTypeOps
    recurse = makeRecurseM ops

    descend :: DescendM InferTypeM InferTypeOps
    descend = makeDescendM ops

    doExpression :: Infer A.Expression
    doExpression outer
        = case outer of
            -- Literals are what we're really looking for here.
            A.Literal m t lr ->
             do t' <- recurse t
                scrubMobile $ do
                  ctx <- getTypeContext
                  let wantT = case (ctx, t') of
                                -- No type specified on the literal,
                                -- but there's a context, so use that.
                                (Just ct, A.Infer) -> ct
                                -- Use the explicit type of the literal, or the
                                -- default.
                                _ -> t'
                  (realT, realLR) <- doLiteral (wantT, lr)
                  return $ A.Literal m realT realLR

            -- Expressions that aren't literals, but that modify the type
            -- context.
            A.SizeExpr _ _ -> noTypeContext $ descend outer
            A.Conversion _ _ _ _ -> noTypeContext $ descend outer
            A.FunctionCall m n es ->
               do (n', es') <- doFunctionCall m (n, es)
                  return $ A.FunctionCall m n' es'
            A.IntrinsicFunctionCall _ _ _ -> noTypeContext $ descend outer
            A.SubscriptedExpr m s e ->
               do ctx <- getTypeContext
                  e' <- inTypeContext (ctx >>= unsubscriptType s) $ recurse e
                  t <- astTypeOf e'
                  s' <- recurse s >>= fixSubscript t
                  return $ A.SubscriptedExpr m s' e'
            A.BytesInExpr _ _ -> noTypeContext $ descend outer
            -- FIXME: ExprConstr
            -- FIXME: AllocMobile

            A.ExprVariable m v ->
              do ctx <- getTypeContext
                 v' <- recurse v
                 derefVariableIfNeeded ctx v' >>* A.ExprVariable m
            -- Other expressions don't modify the type context.
            _ -> descend outer

    doFunctionCall :: Meta -> Infer (A.Name, [A.Expression])
    doFunctionCall m (n, es) = do
      if isOperator (A.nameName n)
        then
              -- for operators, resolve the function name, based on the type
           do let opDescrip = "\"" ++ (A.nameName n) ++ "\" "
                    ++ case length es of
                         1 -> "unary"
                         2 -> "binary"
                         n -> show n ++ "-ary"

              operators <- get >>* csOperators

              resolvedOps <- sequence [ do ts' <- mapM (underlyingType m) ts
                                           rt' <- underlyingType m rt
                                           return (op, n, rt', ts')
                                      | (op, n, rt, ts) <- operators
                                      ]
                             -- The nubBy will ensure that only one definition remains for each
                             -- set of type-arguments, and will keep the first definition in the
                             -- list (which will be the most recent)
                             >>* nubBy opsMatch

              ctx <- (getTypeContext >>* fromMaybe A.Infer) >>= underlyingType m
              let findOperatorTs :: [Maybe A.Type] -> [(A.Name, [A.Type])]
                  findOperatorTs mts
                    = [ (opFuncName, ts)
                      | (raw, opFuncName, rt, ts) <- resolvedOps
                      -- Must be right operator:
                      , raw == A.nameName n
                      -- Must be right arity:
                      , length ts == length mts
                      -- Must have right argument types:
                      , and $ zipWith (maybe True) (map typeEqForOp ts) mts
                      -- Must have right return type:
                      , ctx == A.Infer || ctx `typeEqForOp` rt
                      ]

                  pickTypes :: [Maybe A.Type] -> [Maybe A.Type]
                  pickTypes mts = case findOperatorTs mts of
                    -- Exactly one match; use it:
                    [(_, ts)] -> map Just ts
                    -- No match, or multiple matches, no change:
                    _ -> mts

              -- We have to catch errors here because if it's an operator inside
              -- an operator, the type-getting will fail because we haven't resolved
              -- the inner operator yet.
              origTs <- sequence [(astTypeOf e >>= underlyingType m) `catchError` (const $ return A.Infer) | e <- es]

              es' <- mapM (uncurry inTypeContext)
                       $ zip (pickTypes [case t of
                                           A.Infer -> Nothing
                                           _ -> Just t
                                        | t <- origTs])
                             (map recurse es)

              tes <- sequence [underlyingTypeOf m e `catchError` (const $ return A.Infer) | e <- es']           

              case findOperatorTs $ map Just tes of
                [] -> case ctx of
                  A.Infer -> diePC m $ formatCode "No matching % operator definition found for types: %" opDescrip tes
                  _ -> diePC m $ formatCode ("No matching % operator definition found for types: %"
                        ++ " that returns type: % (original types: %)") opDescrip tes ctx origTs
                [poss] -> return (fst poss, es')
                posss -> dieP m $ "Ambigious " ++ opDescrip ++ " operator, matches definitions: "
                                ++ show (map (transformPair A.nameMeta showOccam) posss)
        else
           do (_, fs) <- lift $ checkFunction m n
              doActuals m n fs (direct, const return) es >>* (,) n
      where
        direct = error "Cannot direct channels passed to FUNCTIONs"

        opsMatch (opA, _, _, tsA) (opB, _, _, tsB) = (opA == opB) && (tsA `typesEqForOp` tsB)

        typesEqForOp :: [A.Type] -> [A.Type] -> Bool
        typesEqForOp tsA tsB = (length tsA == length tsB) && (and $ zipWith typeEqForOp tsA tsB)

        typeEqForOp :: A.Type -> A.Type -> Bool
        typeEqForOp (A.Array ds t) (A.Array ds' t')
          = (length ds == length ds') && typeEqForOp t t'
        -- Since we auto-dereference mobiles that are passed to operators, we must
        -- auto-skip mobile-ness when checking the types, so that we can still
        -- infer properly if the user is passing a MOBILE INT instead of an INT.
        --  This does mean you can't overload operators on MOBILE INT differently
        -- than INT, but I don't see how we could allow that sensibly anyway
        typeEqForOp (A.Mobile t) t'
          = typeEqForOp t t'
        typeEqForOp t (A.Mobile t')
          = typeEqForOp t t'
        typeEqForOp t t' = t == t'

    doActuals :: (PolyplateM a InferTypeOps () InferTypeM, Data a) => Meta -> A.Name -> [A.Formal] ->
      (Meta -> A.Direction -> Infer a, A.Type -> Infer a) -> Infer [a]
    doActuals m n fs applyDir_Deref as
        =  do lift $ checkActualCount m n fs as
              sequence [doActual m applyDir_Deref t a | (A.Formal _ t _, a) <- zip fs as]

    -- First function directs, second function dereferences if needed
    doActual :: (PolyplateM a InferTypeOps () InferTypeM, Data a) =>
      Meta -> (Meta -> A.Direction -> Infer a, A.Type -> Infer a) -> A.Type -> Infer a
    doActual m (applyDir, _) (A.ChanEnd dir _ _) a = recurse a >>= applyDir m dir
    doActual m (_, deref) t a = inTypeContext (Just t) $ recurse a >>= deref t
                        

    doDimension :: Infer A.Dimension
    doDimension dim = inTypeContext (Just A.Int) $ descend dim

    doSubscript :: Infer A.Subscript
    doSubscript s = inTypeContext (Just A.Int) $ descend s

    doExpressionList :: [A.Type] -> Infer A.ExpressionList
    doExpressionList ts el
        = case el of
            A.FunctionCallList m n es ->
               do (n', es') <- doFunctionCall m (n, es)
                  return $ A.FunctionCallList m n' es'
            A.ExpressionList m es ->
               do es' <- sequence [inTypeContext (Just t) $ recurse e
                                   | (t, e) <- zip ts es]
                  es'' <- mapM (uncurry $ inferAllocMobile m) $ zip ts es'
                  return $ A.ExpressionList m es''
            A.AllocChannelBundle {} -> return el

    doReplicator :: Infer A.Replicator
    doReplicator rep
        = case rep of
            A.For _ _ _ _ -> inTypeContext (Just A.Int) $ descend rep
            A.ForEach _ _ -> noTypeContext $ descend rep

    doAlternative :: Infer A.Alternative
    doAlternative (A.Alternative m pre v im p)
      = do pre' <- inTypeContext (Just A.Bool) $ recurse pre
           v' <- recurse v >>= derefVariableIfNeeded Nothing
           im' <- doInputMode v' im
           p' <- recurse p
           return $ A.Alternative m pre' v' im' p'
    doAlternative (A.AlternativeSkip m pre p)
      = do pre'  <- inTypeContext (Just A.Bool) $ recurse pre
           p' <- recurse p
           return $ A.AlternativeSkip m pre' p'

    doInputMode :: A.Variable -> Infer A.InputMode
    doInputMode v (A.InputSimple m iis)
      = do ts <- protocolItems m v >>* either id (const [])
           iis' <- sequence [doInputItem t ii
                            | (t, ii) <- zip ts iis]
           return $ A.InputSimple m iis'
    doInputMode v (A.InputCase m sv)
      = do ct <- astTypeOf v
           inTypeContext (Just ct) (recurse sv) >>* A.InputCase m
    doInputMode _ (A.InputTimerRead m ii)
      = doInputItem A.Int ii >>* A.InputTimerRead m
    doInputMode _ im = inTypeContext (Just A.Int) $ descend im

    doInputItem :: A.Type -> Infer A.InputItem
    doInputItem t (A.InVariable m v)
      = (inTypeContext (Just t) (recurse v)
           >>= derefVariableIfNeeded (Just t)
        ) >>* A.InVariable m
    doInputItem t (A.InCounted m cv av)
      = do cv' <- inTypeContext (Just A.Int) (recurse cv)
                    >>= derefVariableIfNeeded (Just A.Int)
           av' <- inTypeContext (Just t) (recurse av)
                    >>= derefVariableIfNeeded (Just t)
           return $ A.InCounted m cv' av'

    doVariant :: Infer A.Variant
    doVariant (A.Variant m n iis p)
      = do ctx <- getTypeContext
           ets <- case ctx of
             Just x -> protocolItems m x
             Nothing -> dieP m "Could not deduce protocol"
           case ets of
             Left {} -> dieP m "Simple protocol expected during input CASE"
             Right ps -> case lookup n ps of
               Nothing -> diePC m $ formatCode "Name % is not part of protocol %"
                 n (fromJust ctx)
               Just ts -> do iis' <- sequence [doInputItem t ii
                                              | (t, ii) <- zip ts iis]
                             p' <- recurse p
                             return $ A.Variant m n iis' p'

    doStructured :: ( PolyplateM (A.Structured t) InferTypeOps () InferTypeM
                    , PolyplateM (A.Structured t) () InferTypeOps InferTypeM
                    , Data t) => Infer (A.Structured t)

    doStructured (A.Spec mspec s@(A.Specification m n st) body)
        =  do (st', wrap) <- runReaderT (doSpecType n st) body
              -- Update the definition of each name after we handle it.
              modifyName n (\nd -> nd { A.ndSpecType = st' })
              wrap (recurse body) >>* A.Spec mspec (A.Specification m n st')
    doStructured s = descend s

    -- The second parameter is a modifier (wrapper) for the descent into the body
    doSpecType :: ( PolyplateM (A.Structured t) InferTypeOps () InferTypeM
                  , PolyplateM (A.Structured t) () InferTypeOps InferTypeM
                  , Data t) => A.Name -> A.SpecType -> ReaderT (A.Structured t) InferTypeM
      (A.SpecType, InferTypeM (A.Structured a) -> InferTypeM (A.Structured a))
    doSpecType n st
        = case st of
            A.Place _ _ -> lift $ inTypeContext (Just A.Int) $ descend st >>* addId
            A.Is m am t (A.ActualVariable v) ->
               do am' <- lift $ recurse am
                  t' <- lift $ recurse t
                  v' <- lift $ inTypeContext (Just t') $ recurse v
                    >>= derefVariableIfNeeded (Just t')
                  vt <- lift $ astTypeOf v'
                  (t'', v'') <- case (t', vt) of
                    (A.Infer, A.Chan attr innerT) ->
                         do dirs <- ask >>= (lift . findDir n)
                            case nub dirs of
                              [dir] ->
                                do let tEnd = A.ChanEnd dir (dirAttr dir attr) innerT
                                   return (tEnd, A.DirectedVariable m dir v')
                              _ -> return (vt, v') -- no direction, or two
                    (A.Infer, _) -> return (vt, v')
                    (A.ChanEnd dir _ _, _) -> do v'' <- lift $ lift $ makeEnd m dir v'
                                                 return (t', v'')
                    (A.Array _ (A.ChanEnd dir _ _), _) ->
                                         do v'' <- lift $ lift $ makeEnd m dir v'
                                            return (t', v'')
                    (A.Chan cattr cinnerT, A.ChanEnd dir _ einnerT)
                      -> do cinnerT' <- lift $ recurse cinnerT
                            einnerT' <- lift $ recurse einnerT
                            if cinnerT' /= einnerT'
                              then lift $ diePC m $ formatCode "Inner types of channels do not match in type inference: % %" cinnerT' einnerT'
                              else return (vt, v')
                    (A.Chan attr innerT, A.Chan {}) ->
                         do dirs <- ask >>= (lift . findDir n)
                            case nub dirs of
                              [dir] ->
                                do let tEnd = A.ChanEnd dir (dirAttr dir attr) innerT
                                   return (tEnd, A.DirectedVariable m dir v')
                              _ -> return (t', v') -- no direction, or two
                    _ -> return (t', v')
                  return $ addId $ A.Is m am' t'' $ A.ActualVariable v''
            A.Is m am t (A.ActualExpression e) -> lift $
               do am' <- recurse am
                  t' <- recurse t
                  e' <- inTypeContext (Just t') $ recurse e
                  t'' <- case t' of
                           A.Infer -> astTypeOf e'
                           A.Array ds _ | A.UnknownDimension `elem` ds -> astTypeOf e'
                           _ -> return t'
                  return $ addId $ A.Is m am' t'' (A.ActualExpression e')
            A.Is m am t (A.ActualClaim v) -> lift $
               do am' <- recurse am
                  t' <- recurse t
                  v' <- inTypeContext (Just t') $ recurse v
                  t'' <- case t' of
                           A.Infer -> astTypeOf (A.ActualClaim v')
                           _ -> return t'
                  am'' <- case t'' of
                            -- CLAIMed channel bundles are ValAbbrev, as they may
                            -- not be altered:
                            A.ChanDataType {} ->
                              do modifyName n $ \nd -> nd { A.ndAbbrevMode = A.ValAbbrev }
                                 return A.ValAbbrev
                            -- CLAIMed normal channels are as before:
                            _ -> return am'
                  return $ addId $ A.Is m am'' t'' (A.ActualClaim v')
            A.Is m am t (A.ActualChannelArray vs) ->
               -- No expressions in this -- but we may need to infer the type
               -- of the variable if it's something like "cs IS [c]:".
               do t' <- lift $ recurse t
                  vs' <- lift $ mapM recurse vs >>= case t' of
                    A.Infer -> return
                    A.Array _ (A.Chan {}) -> return
                    A.Array _ (A.ChanEnd dir _ _) -> mapM (lift . makeEnd m dir)
                    _ -> const $ dieP m "Cannot coerce non-channels into channels"
                  let dim = makeDimension m $ length vs'
                  t'' <- lift $ case (t', vs') of
                           (A.Infer, (v:_)) ->
                             do elemT <- astTypeOf v
                                return $ addDimensions [dim] elemT
                           (A.Infer, []) ->
                             dieP m "Cannot infer type of empty channel array"
                           _ -> return $ applyDimension dim t'
                  (t''', f) <- case t'' of
                    A.Array ds (A.Chan attr innerT) -> do
                      dirs <- ask >>= (lift . findDir n)
                      case nub dirs of
                        [dir] -> return (A.Array ds $ A.ChanEnd dir (dirAttr dir attr) innerT
                                        ,A.DirectedVariable m dir)
                        _ -> return (t'', id)
                    _ -> return (t'', id)
                  return $ addId $ A.Is m am t''' $ A.ActualChannelArray $ map f vs'
            A.Function m sm ts fs mbody -> lift $
               do sm' <- recurse sm
                  ts' <- recurse ts
                  fs' <- recurse fs
                  sel' <- case mbody of
                    Just (Left sel) -> doFuncDef ts sel >>* (Just . Left)
                    _ -> return mbody
                  mOp <- functionOperator n
                  let func = A.Function m sm' ts' fs' sel'
                  case mOp of
                    Just raw -> do
                      ts <- mapM astTypeOf fs
                      rt <- case ts' of
                              [t] -> return t
                              _ -> dieP m "Operator must have exactly one return"
                      let before, after :: InferTypeM ()
                          before = modify $ \cs -> cs { csOperators = (raw, n, rt, ts) : csOperators cs }
                          after = modify $ \cs -> cs { csOperators = tail (csOperators cs)}
                      return (func
                             ,\m -> do before
                                       x <- m
                                       after
                                       return x)
                    _ -> return func >>* addId
            A.Retypes m am t v ->
              do t' <- lift $ recurse t
                 lift $ inTypeContext (Just t') $
                   (recurse v >>= derefVariableIfNeeded (Just t')) >>*
                    (addId . A.Retypes m am t')
            A.RetypesExpr _ _ _ _ -> lift $ noTypeContext $ descend st >>* addId
            -- For PROCs that take any channels without direction,
            -- we must determine if we can infer a specific direction
            -- for that channel
            A.Proc m sm fs body -> lift $
               do body' <- recurse body
                  fs' <- mapM (processFormal body') fs
                  return $ addId $ A.Proc m sm fs' body'
               where
                 processFormal body f@(A.Formal am t n)
                  = do t' <- recurse t
                       case t' of
                        A.Chan attr innerT ->
                         do dirs <- findDir n body
                            case nub dirs of
                              [dir] ->
                                do let t' = A.ChanEnd dir (dirAttr dir attr) innerT
                                       f' = A.Formal am t' n
                                   modifyName n (\nd -> nd {A.ndSpecType =
                                     A.Declaration m t'})
                                   return f'
                              _ -> return $ A.Formal am t' n -- no direction, or two
                        _ -> do modifyName n (\nd -> nd {A.ndSpecType =
                                     A.Declaration m t'})
                                return $ A.Formal am t' n
            _ -> lift $ descend st >>* addId
      where
        addId :: a -> (a, b -> b)
        addId a = (a, id)
        
        -- | This is a bit ugly: walk down a Structured to find the single
        -- ExpressionList that must be in there.
        -- (This can go away once we represent all functions in the new Process
        -- form.)
        doFuncDef :: [A.Type] -> Infer (A.Structured A.ExpressionList)
        doFuncDef ts (A.Spec m (A.Specification m' n st) s)
            =  do (st', wrap) <- runReaderT (doSpecType n st) s
                  modifyName n (\nd -> nd { A.ndSpecType = st' })
                  s' <- wrap $ doFuncDef ts s
                  return $ A.Spec m (A.Specification m' n st') s'
        doFuncDef ts (A.ProcThen m p s)
            =  do p' <- recurse p
                  s' <- doFuncDef ts s
                  return $ A.ProcThen m p' s'
        doFuncDef ts (A.Only m el)
            =  do el' <- doExpressionList ts el
                  return $ A.Only m el'

        -- findDir only really needs to descend operating on Variables
        -- But since this is called by doStructured, that would require doStructured
        -- to have an extra constraint that the Structured supports descent into
        -- Variables.  But that constraint, in turn, is not satisfied when we build
        -- our ops using extOpMS.  Rather than fix all the constraints, I've decided
        -- to adopt a slightly sneaky approach, and build a set of ops for findDir
        -- with the same type as the one for infer types (thus the constraints
        -- don't change), but where everything apart from the Variable operation
        -- is a call to descend.
        --
        -- Also, to fit with the normal ops, we must do so in the PassM monad.
        --  Normally we would do this pass in a StateT monad, but to slip inside
        -- PassM, I've used an IORef instead.
        findDir :: ( PolyplateM a InferTypeOps () InferTypeM
                   , PolyplateM a () InferTypeOps InferTypeM
                   ) => A.Name -> a -> InferTypeM [A.Direction]
        findDir n x
          = do r <- liftIO $ newIORef []
               makeRecurseM (makeOps r) x
               liftIO $ readIORef r
          where
            makeOps :: IORef [A.Direction] -> InferTypeOps
            makeOps r = ops
              where
                ops :: InferTypeOps
                ops = baseOp
                    `extOpMS` (ops, descend)
                    `extOpM` descend
                    `extOpM` descend
                    `extOpM` descend
                    `extOpM` descend
                    `extOpM` descend
                    `extOpM` descend
                    `extOpM` (doVariable r)
                    `extOpM` descend
                descend :: DescendM InferTypeM InferTypeOps
                descend = makeDescendM ops

            -- This will cover everything, since we will have inferred the direction
            -- specifiers before applying this function.
            doVariable :: IORef [A.Direction] -> Infer A.Variable
            doVariable r v@(A.DirectedVariable _ dir (A.Variable _ n')) | n == n'
              = liftIO $ modifyIORef r (dir:) >> return v
            doVariable r v@(A.DirectedVariable _ dir
              (A.SubscriptedVariable _ _ (A.Variable _ n'))) | n == n'
              = liftIO $ modifyIORef r (dir:) >> return v
            doVariable r v = makeDescendM (makeOps r) v

    doProcess :: Infer A.Process
    doProcess p
        = case p of
            A.Assign m vs el ->
                  -- We do not dereference variables on the LHS of an assignment,
                  -- instead we promote the things on the RHS to allocations if
                  -- needed.  After all, if the user does something like:
                  -- xs := "flibble"
                  -- where xs is a mobile array, we definitely want to allocate
                  -- the RHS, rather than dereference the possibly undefined LHS.
               do vs' <- noTypeContext $ recurse vs
                  ts <- mapM astTypeOf vs'
                  el' <- doExpressionList ts el
                  return $ A.Assign m vs' el'
            -- We don't dereference any of the channel variables, the backend can
            -- handle that.
            A.Output m v ois ->
               do v' <- recurse v
                  -- At this point we must resolve the "c ! x" ambiguity:
                  -- we definitely know what c is, and we must know what x is
                  -- before trying to infer its type.
                  tagged <- isTagged v'
                  if tagged
                    -- Tagged protocol -- convert (wrong) variable to tag.
                    then case ois of
                           ((A.OutExpression _ (A.ExprVariable _ (A.Variable _ wrong))):ois) ->
                             do tag <- nameToUnscoped wrong
                                ois' <- doOutputItems m v' (Just tag) ois
                                return $ A.OutputCase m v' tag ois'
                           _ -> diePC m $ formatCode "This channel carries a variant protocol; expected a list starting with a tag, but found %" ois
                    -- Regular protocol -- proceed as before.
                    else do ois' <- doOutputItems m v' Nothing ois
                            return $ A.Output m v' ois'
            A.OutputCase m v tag ois ->
               do v' <- recurse v
                  ois' <- doOutputItems m v' (Just tag) ois
                  return $ A.OutputCase m v' tag ois'
            A.If _ _ -> inTypeContext (Just A.Bool) $ descend p
            A.Case m e so ->
               do e' <- recurse e
                  t <- astTypeOf e'
                  so' <- inTypeContext (Just t) $ recurse so
                  return $ A.Case m e' so'
            A.While _ _ _ -> inTypeContext (Just A.Bool) $ descend p
            A.Processor _ _ _ -> inTypeContext (Just A.Int) $ descend p
            A.ProcCall m n as ->
               do fs <- lift $ checkProc m n
                  as' <- doActuals m n fs
                    (\m dir (A.ActualVariable v) -> lift $ liftM A.ActualVariable $ makeEnd m dir v
                    ,\t a -> case a of
                      A.ActualVariable v -> derefVariableIfNeeded (Just t) v >>* A.ActualVariable
                      _ -> return a
                    ) as
                  return $ A.ProcCall m n as'
            p@(A.IntrinsicProcCall m n as) ->
               case lookup n intrinsicProcs of
                 Nothing -> descend p -- Will fail type-checking anyway
                 Just params -> sequence [inTypeContext (Just t) $
                   case a of
                     A.ActualVariable v ->
                       (recurse v >>= derefVariableIfNeeded (Just t)) >>* A.ActualVariable
                     _ -> descend a
                   | (a, (_,t,_)) <- zip as params] >>* A.IntrinsicProcCall m n                   
            A.Input m v im@(A.InputSimple {})
              -> do v' <- recurse v
                    im' <- doInputMode v' im
                    return $ A.Input m v' im'
            A.Input m v im@(A.InputCase {})
              -> do v' <- recurse v
                    im' <- doInputMode v' im
                    return $ A.Input m v' im'
            _ -> descend p
      where
        -- | Does a channel carry a tagged protocol?
        isTagged :: A.Variable -> InferTypeM Bool
        isTagged c
            =  do protoT <- lift $ checkChannel A.DirOutput c
                  case protoT of
                    A.UserProtocol n ->
                       do st <- specTypeOfName n
                          case st of
                            A.ProtocolCase _ _ -> return True
                            _ -> return False
                    _ -> return False

        doOutputItems :: Meta -> A.Variable -> Maybe A.Name
                         -> Infer [A.OutputItem]
        doOutputItems m v tag ois
            =  do chanT <- lift $ checkChannel A.DirOutput v
                  ts <- lift $ protocolTypes m chanT tag
                  sequence [doOutputItem t oi | (t, oi) <- zip ts ois]

        doOutputItem :: A.Type -> Infer A.OutputItem
        doOutputItem (A.Counted ct at) (A.OutCounted m ce ae)
            =  do ce' <- inTypeContext (Just ct) $ recurse ce
                  ae' <- inTypeContext (Just at) $ recurse ae
                  return $ A.OutCounted m ce' ae'
        doOutputItem A.Any o = noTypeContext $ recurse o
        doOutputItem t (A.OutExpression m e)
          = inTypeContext (Just t) (recurse e >>= inferAllocMobile m t)
              >>* A.OutExpression m

    doVariable :: Infer A.Variable
    doVariable (A.SubscriptedVariable m s v)
        =  do v' <- noTypeContext (recurse v) >>= derefVariableIfNeeded Nothing
              t <- astTypeOf v'
              s' <- recurse s >>= fixSubscript t
              return $ A.SubscriptedVariable m s' v'
    doVariable v = descend v

    derefVariableIfNeeded :: Maybe (A.Type) -> Infer A.Variable
    derefVariableIfNeeded ctxOrig v
        =  do ctx <- (T.sequence . fmap (resolveUserType (findMeta v))) ctxOrig
              underT <- astTypeOf v >>= resolveUserType (findMeta v)
              case (ctx, underT) of
                (Just (A.Mobile {}), A.Mobile {}) -> return v
                (_, A.Mobile {}) -> return $ A.DerefVariable (findMeta v) v
                _ -> return v
    

    -- | Resolve the @v[s]@ ambiguity: this takes the type that @v@ is, and
    -- returns the correct 'Subscript'.
    fixSubscript :: A.Type -> Infer A.Subscript
    fixSubscript t s@(A.Subscript m _ (A.ExprVariable _ (A.Variable _ wrong)))
        =  do underT <- resolveUserType m t
              case underT of
                A.Record _ ->
                  do n <- nameToUnscoped wrong
                     return $ A.SubscriptField m n
                A.ChanDataType {} ->
                  do n <- nameToUnscoped wrong
                     return $ A.SubscriptField m n
                _ -> return s
    fixSubscript _ s = return s

    -- | Given a name that should really have been a tag, make it one.
    nameToUnscoped :: A.Name -> InferTypeM A.Name
    nameToUnscoped n@(A.Name m _)
        =  do nd <- lookupName n
              findUnscopedName (A.Name m (A.ndOrigName nd))

    -- | Process a 'LiteralRepr', taking the type it's meant to represent or
    -- 'Infer', and returning the type it really is.
    doLiteral :: Infer (A.Type, A.LiteralRepr)
    doLiteral (wantT, lr)
        = case lr of
            A.ArrayListLiteral m aes ->
               do (t, aes') <-
                    doArrayElem wantT aes
                  lr' <- case aes' of
                    A.Several _ ss -> buildTable t ss
                    _ -> return $ A.ArrayListLiteral m aes'
                  return (t, lr')
            _ ->
               do lr' <- descend lr
                  (defT, isT) <-
                    case lr' of
                      A.RealLiteral _ _ -> return (A.Real32, isRealType)
                      A.IntLiteral _ _ -> return (A.Int, isIntegerType)
                      A.HexLiteral _ _ -> return (A.Int, isIntegerType)
                      A.ByteLiteral _ _ -> return (A.Byte, isIntegerType)
                      _ -> dieP m $ "Unexpected LiteralRepr: " ++ show lr'
                  underT <- resolveUserType m wantT
                  case (wantT, isT underT) of
                    (A.Infer, _) -> return (defT, lr')
                    (_, True) -> return (wantT, lr')
                    (_, False) -> diePC m $ formatCode "Literal of default type % is not valid for type %" defT wantT
      where
        m = findMeta lr

        doArrayElem :: A.Type -> A.Structured A.Expression -> InferTypeM (A.Type, A.Structured A.Expression)
        doArrayElem wantT (A.Spec m spec body)
        -- A replicator: strip off a subscript and keep going
            =  do underT <- resolveUserType m wantT
                  subT <- trivialSubscriptType m underT
                  dim <- case underT of
                    A.Array (dim:_) _ -> return dim
                    A.Infer -> return A.UnknownDimension
                    _ -> diePC m $ formatCode "Unexpected type in array constructor: %" underT
                  (t, body') <- doArrayElem subT body
                  specAndBody' <- doStructured $ A.Spec m spec body'
                  return (applyDimension dim wantT, specAndBody')
        -- A table: this could be an array or a record.
        doArrayElem wantT (A.Several m aes)
            =  do underT <- resolveUserType m wantT
                  case underT of
                    A.Array _ _ ->
                       do subT <- trivialSubscriptType m underT
                          (elemT, aes') <- doElems subT aes
                          let dim = makeDimension m (length aes)
                          return (addDimensions [dim] elemT, A.Several m aes')
                    A.Record _ ->
                       do nts <- recordFields m underT
                          aes <- sequence [doArrayElem t ae >>* snd
                                           | ((_, t), ae) <- zip nts aes]
                          return (wantT, A.Several m aes)
                    -- If we don't know, assume it's an array.
                    A.Infer ->
                       do (elemT, aes') <- doElems A.Infer aes
                          when (elemT == A.Infer) $
                            dieP m "Cannot infer type of (empty?) array"
                          let dims = [makeDimension m (length aes)]
                          return (addDimensions dims elemT,
                                  A.Several m aes')
                    _ -> diePC m $ formatCode "Table literal is not valid for type %" wantT
          where
            doElems :: A.Type -> [A.Structured A.Expression] -> InferTypeM (A.Type, [A.Structured A.Expression])
            doElems t aes
                =  do ts <- mapM (\ae -> doArrayElem t ae >>* fst) aes
                      let bestT = foldl betterType t ts
                      aes' <- mapM (\ae -> doArrayElem bestT ae >>* snd) aes
                      return (bestT, aes')
        -- An expression: descend into it with the right context.
        doArrayElem wantT (A.Only m e)
            =  do e' <- inTypeContext (Just wantT) $ doExpression e
                  t <- astTypeOf e'
                  lift $ checkType (findMeta e') wantT t
                  return (t, A.Only m e')

        -- | Turn a raw table literal into the appropriate combination of
        -- arrays and records.
        buildTable :: A.Type -> [A.Structured A.Expression] -> InferTypeM A.LiteralRepr
        buildTable t aes
            =  do underT <- resolveUserType m t
                  case underT of
                    A.Array _ _ ->
                       do elemT <- trivialSubscriptType m t
                          aes' <- mapM (buildElem elemT) aes
                          return $ A.ArrayListLiteral m $ A.Several m aes'
                    A.Record _ ->
                       do nts <- recordFields m underT
                          aes' <- sequence [buildExpr elemT ae
                                            | ((_, elemT), ae) <- zip nts aes]
                          return $ A.RecordLiteral m aes'
          where
            buildExpr :: A.Type -> A.Structured A.Expression -> InferTypeM A.Expression
            buildExpr t (A.Several _ aes)
                =  do lr <- buildTable t aes
                      return $ A.Literal m t lr
            buildExpr _ (A.Only _ e) = return e

            buildElem :: A.Type -> Infer (A.Structured A.Expression)
            buildElem t ae
                =  do underT <- resolveUserType m t
                      case (underT, ae) of
                        (A.Array _ _, A.Several _ aes) ->
                           do A.ArrayListLiteral _ aes' <- buildTable t aes
                              return aes'
                        (A.Record _, A.Several {}) ->
                           do e <- buildExpr t ae
                              return $ A.Only m e
                        (_, A.Only {}) -> return ae

--}}}
