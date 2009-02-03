{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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
module OccamTypes (inferTypes, checkTypes, addDirections) where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Function (on)
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Traversable as T

import qualified AST as A
import CompState
import Errors
import EvalConstants
import Intrinsics
import Metadata
import Pass
import qualified Properties as Prop
import ShowCode
import Traversal
import Types
import Utils

-- | A successful check.
ok :: PassM ()
ok = return ()

--{{{  type checks

-- | Are two types the same?
sameType :: A.Type -> A.Type -> PassM Bool
sameType (A.Array (A.Dimension e1 : ds1) t1)
         (A.Array (A.Dimension e2 : ds2) t2)
    =  do n1 <- evalIntExpression e1
          n2 <- evalIntExpression e2
          same <- sameType (A.Array ds1 t1) (A.Array ds2 t2)
          return $ (n1 == n2) && same
sameType (A.Array (A.UnknownDimension : ds1) t1)
         (A.Array (A.UnknownDimension : ds2) t2)
    = sameType (A.Array ds1 t1) (A.Array ds2 t2)
-- We might be dealing with channels of arrays, so we must dig through channels:
sameType (A.Chan _ ta) (A.Chan _ tb) = sameType ta tb
sameType (A.ChanEnd dira _ ta) (A.ChanEnd dirb _ tb)
  = liftM (dira == dirb &&) (sameType ta tb)
sameType (A.Mobile ta) (A.Mobile tb) = sameType ta tb
-- Resolve user data types:
sameType ta@(A.UserDataType {}) tb
  = do ta' <- resolveUserType emptyMeta ta
       sameType ta' tb
sameType ta tb@(A.UserDataType {})
  = do tb' <- resolveUserType emptyMeta tb
       sameType ta tb'
sameType a b = return $ a == b

-- | Check that the second dimension can be used in a context where the first
-- is expected.
isValidDimension :: A.Dimension -> A.Dimension -> PassM Bool
isValidDimension A.UnknownDimension A.UnknownDimension = return True
isValidDimension A.UnknownDimension (A.Dimension _) = return True
isValidDimension (A.Dimension e1) (A.Dimension e2)
    =  do n1 <- evalIntExpression e1
          n2 <- evalIntExpression e2
          return $ n1 == n2
isValidDimension _ _ = return False

-- | Check that the second second of dimensions can be used in a context where
-- the first is expected.
areValidDimensions :: [A.Dimension] -> [A.Dimension] -> PassM Bool
areValidDimensions [] [] = return True
areValidDimensions (d1:ds1) (d2:ds2)
    = do valid <- isValidDimension d1 d2
         if valid
           then areValidDimensions ds1 ds2
           else return False
areValidDimensions _ _ = return False

-- | Check that a type we've inferred matches the type we expected.
checkType :: Meta -> A.Type -> A.Type -> PassM ()
checkType m et rt
    = case (et, rt) of
        (A.Infer, _) -> ok
        (A.Array ds t, A.Array ds' t') ->
          do valid <- areValidDimensions ds ds'
             if valid
               then checkType m t t'
               else bad
        (A.Mobile t, A.Mobile t') -> checkType m t t'
        _ ->
          do same <- sameType rt et
             when (not same) $ bad
  where
    bad :: PassM ()
    bad = diePC m $ formatCode ("Type mismatch: found %, expected % ("++show (rt,et)++")") rt et

-- | Check a type against a predicate.
checkTypeClass :: (A.Type -> Bool) -> String -> Meta -> A.Type -> PassM ()
checkTypeClass f adjective m rawT
    =  do t <- underlyingType m rawT
          if f t
            then ok
            else diePC m $ formatCode ("Expected " ++ adjective ++ " type; found %") t

-- | Check that a type is numeric.
checkNumeric :: Meta -> A.Type -> PassM ()
checkNumeric = checkTypeClass isNumericType "numeric"

-- | Check that a type is integral.
checkInteger :: Meta -> A.Type -> PassM ()
checkInteger = checkTypeClass isIntegerType "integer"

-- | Check that a type is case-selectable.
checkCaseable :: Meta -> A.Type -> PassM ()
checkCaseable = checkTypeClass isCaseableType "case-selectable"

-- | Check that a type is scalar.
checkScalar :: Meta -> A.Type -> PassM ()
checkScalar = checkTypeClass isScalarType "scalar"

-- | Check that a type is usable as a 'DataType'
checkDataType :: Meta -> A.Type -> PassM ()
checkDataType = checkTypeClass isDataType "data"

-- | Check that a type is communicable.
checkCommunicable :: Meta -> A.Type -> PassM ()
checkCommunicable m (A.Counted ct rawAT)
    =  do checkInteger m ct
          at <- resolveUserType m rawAT
          case at of
            A.Array (A.UnknownDimension:ds) t ->
               do checkCommunicable m t
                  mapM_ (checkFullDimension m) ds
            _ -> dieP m "Expected array type with unknown first dimension"
checkCommunicable m A.Any = ok
checkCommunicable m t = checkTypeClass isCommunicableType "communicable" m t

-- | Check that a type is a sequence.
checkSequence :: Bool -> Meta -> A.Type -> PassM ()
checkSequence mobileAllowed = checkTypeClass (isSequenceType mobileAllowed) "array or list"

-- | Check that a type is an array.
checkArray :: Meta -> A.Type -> PassM ()
checkArray m rawT
    =  do t <- resolveUserType m rawT
          case t of
            A.Array _ _ -> ok
            _ -> diePC m $ formatCode "Expected array type; found %" t

-- | Check that a dimension isn't unknown.
checkFullDimension :: Meta -> A.Dimension -> PassM ()
checkFullDimension m A.UnknownDimension
    = dieP m $ "Type contains unknown dimensions"
checkFullDimension _ _ = ok

-- | Check that a type is a list.
checkList :: Meta -> A.Type -> PassM ()
checkList m rawT
    =  do t <- resolveUserType m rawT
          case t of
            A.List _ -> ok
            _ -> diePC m $ formatCode "Expected list type; found %" t

-- | Check the type of an expression.
checkExpressionType :: A.Type -> A.Expression -> PassM ()
checkExpressionType et e = astTypeOf e >>= checkType (findMeta e) et

-- | Check that an expression is of integer type.
checkExpressionInt :: Check A.Expression
checkExpressionInt e = checkExpressionType A.Int e

-- | Check that an expression is of boolean type.
checkExpressionBool :: Check A.Expression
checkExpressionBool e = checkExpressionType A.Bool e

-- | Pick the more specific of a pair of types.
betterType :: A.Type -> A.Type -> A.Type
betterType t1 t2
    = case betterType' t1 t2 of
        Left () -> t1
        Right () -> t2
  where
    betterType' :: A.Type -> A.Type -> Either () ()
    betterType' A.Infer t = Right ()
    betterType' t A.Infer = Left ()
    betterType' t@(A.UserDataType _) _ = Left ()
    betterType' _ t@(A.UserDataType _) = Right ()
    betterType' t1@(A.Array ds1 et1) t2@(A.Array ds2 et2)
      | length ds1 == length ds2 = betterType' et1 et2
      | length ds1 < length ds2  = Left ()
    betterType' t _ = Left ()

--}}}
--{{{  more complex checks

-- | Check that an array literal's length matches its type.
checkArraySize :: Meta -> A.Type -> Int -> PassM ()
checkArraySize m rawT want
    =  do t <- resolveUserType m rawT
          case t of
            A.Array (A.UnknownDimension:_) _ -> ok
            A.Array (A.Dimension e:_) _ ->
               do n <- evalIntExpression e
                  when (n /= want) $
                    dieP m $ "Array literal has wrong number of elements: found " ++ show n ++ ", expected " ++ show want
            _ -> checkArray m t

-- | Check that a record field name is valid.
checkRecordField :: Meta -> A.Type -> A.Name -> PassM ()
checkRecordField m t n
    =  do rfs <- recordFields m t
          let validNames = map fst rfs
          when (not $ n `elem` validNames) $
            diePC m $ formatCode "Invalid field name % in record type %" n t

-- | Check a subscript.
checkSubscript :: Meta -> A.Subscript -> A.Type -> PassM ()
checkSubscript m s rawT
    =  do -- Check the type of the thing being subscripted.
          t <- resolveUserType m rawT
          case s of
            -- A record subscript.
            A.SubscriptField m n ->
              checkRecordField m t n
            -- A sequence subscript.
            A.Subscript _ _ _ -> checkSequence False m t
            -- An array slice.
            _ -> checkArray m t

          -- Check the subscript itself.
          case s of
            A.Subscript m _ e -> checkExpressionInt e
            A.SubscriptFromFor m _ e f ->
              checkExpressionInt e >> checkExpressionInt f
            A.SubscriptFrom m _ e -> checkExpressionInt e
            A.SubscriptFor m _ e -> checkExpressionInt e
            _ -> ok

-- | Check an abbreviation.
-- Is the second abbrev mode a valid abbreviation of the first?
checkAbbrev :: Meta -> A.AbbrevMode -> A.AbbrevMode -> PassM ()
checkAbbrev m orig new
    = case (orig, new) of
        (_, A.Original) -> bad
        (A.ValAbbrev, A.ValAbbrev) -> ok
        (A.ValAbbrev, A.InitialAbbrev) -> ok
        (A.ValAbbrev, _) -> bad
        _ -> ok
  where
    bad :: PassM ()
    bad = dieP m $ "You can't abbreviate " ++ showAM orig ++ " as " ++ showAM new

    showAM :: A.AbbrevMode -> String
    showAM A.Original = "an original declaration"
    showAM A.Abbrev = "a reference abbreviation"
    showAM A.ValAbbrev = "a VAL abbreviation"
    showAM A.InitialAbbrev = "an INITIAL abbreviation"
    showAM A.ResultAbbrev = "a RESULT abbreviation"

-- | Check a list of actuals is the right length for a list of formals.
checkActualCount :: Meta -> A.Name -> [A.Formal] -> [a] -> PassM ()
checkActualCount m n fs as
    =  do when (length fs /= length as) $
            diePC m $ formatCode ("% called with wrong number of arguments; found " ++ (show $ length as) ++ ", expected " ++ (show $ length fs)) n

-- | Check a set of actuals against the formals they're meant to match.
checkActuals :: Meta -> A.Name -> [A.Formal] -> [A.Actual] -> PassM ()
checkActuals m n fs as
    =  do checkActualCount m n fs as
          sequence_ [checkActual f a
                     | (f, a) <- zip fs as]

-- | Check an actual against its matching formal.
checkActual :: A.Formal -> A.Actual -> PassM ()
checkActual (A.Formal newAM et _) a
    =  do rt <- astTypeOf a
          checkType (findMeta a) et rt
          origAM <- case a of
                      A.ActualVariable v -> abbrevModeOfVariable v
                      A.ActualExpression _ -> return A.ValAbbrev
                      A.ActualChannelArray {} -> return A.Abbrev
                      A.ActualClaim {} -> return A.Abbrev
          checkAbbrev (findMeta a) origAM newAM

-- | Check a function exists.
checkFunction :: Meta -> A.Name -> PassM ([A.Type], [A.Formal])
checkFunction m n
    =  do st <- lookupNameOrError n (diePC m $ formatCode "Could not find function %" n) >>* A.ndSpecType
          case st of
            A.Function _ _ rs fs _ -> return (rs, fs)
            _ -> diePC m $ formatCode "% is not a function" n

-- | Check a 'Proc' exists.
checkProc :: Meta -> A.Name -> PassM [A.Formal]
checkProc m n
    =  do st <- specTypeOfName n
          case st of
            A.Proc _ _ fs _ -> return fs
            _ -> diePC m $ formatCode "% is not a procedure" n

-- | Check a function call.
checkFunctionCall :: Meta -> A.Name -> [A.Expression] -> PassM [A.Type]
checkFunctionCall m n es
    =  do (rs, fs) <- checkFunction m n
          checkActuals m n fs (map A.ActualExpression es)
          return rs

-- | Check an intrinsic function call.
checkIntrinsicFunctionCall :: Bool -> Meta -> String -> [A.Expression] -> PassM [A.Type]
checkIntrinsicFunctionCall usedInList m n es
    = case lookup n intrinsicFunctions of
        Just (rs, args) ->
           do when (not usedInList && length rs /= 1) $
                dieP m $ "Function " ++ n ++ " used in an expression returns more than one value"
              let fs = [A.Formal A.ValAbbrev t (A.Name m s)
                        | (t, s) <- args]
              checkActuals m (A.Name m n)
                           fs (map A.ActualExpression es)
              return rs
        Nothing -> dieP m $ n ++ " is not an intrinsic function"

-- | Check a mobile allocation.
checkAllocMobile :: Meta -> A.Type -> Maybe A.Expression -> PassM ()
checkAllocMobile m rawT me
    =  do t <- resolveUserType m rawT
          case t of
            A.Mobile innerT ->
               do case innerT of
                    A.Array ds _ -> ok --mapM_ (checkFullDimension m) ds
                    _ -> ok
                  case me of
                    Just e ->
                       do et <- astTypeOf e
                          checkType (findMeta e) innerT et
                    Nothing -> ok
            _ -> diePC m $ formatCode "Expected mobile type in allocation; found %" t

-- | Check that a variable is writable.
checkWritable :: Check A.Variable
checkWritable v
    =  do am <- abbrevModeOfVariable v
          case am of
            A.ValAbbrev -> dieP (findMeta v) $ "Expected a writable variable"
            _ -> ok

-- | Check that is a variable is a channel that can be used in the given
-- direction.
-- If the direction passed is 'DirUnknown', no direction or sharedness checks
-- will be performed.
-- Return the type carried by the channel.
checkChannel :: A.Direction -> A.Variable -> PassM A.Type
checkChannel wantDir c
    =  do -- Check it's a channel.
          t <- astTypeOf c >>= resolveUserType m
          case t of
            A.ChanEnd dir sh innerT ->
               do -- Check the direction is appropriate 
                  when (wantDir /= dir) $ dieP m $ "Channel directions do not match"
                  -- Check it's not shared in the direction we're using.
                  case sh of
                    A.Unshared -> ok
                    A.Shared -> dieP m $ "Shared channel must be claimed before use"

                  return innerT
            _ -> diePC m $ formatCode ("Expected channel " ++ exp ++ "; found %") t
  where
    exp = case wantDir of
            A.DirInput -> "input-end"
            A.DirOutput -> "output-end"
    m = findMeta c

-- | Check that a variable is a timer.
-- Return the type of the timer's value.
checkTimer :: A.Variable -> PassM A.Type
checkTimer tim
    =  do t <- astTypeOf tim >>= resolveUserType m
          case t of
            A.Timer A.OccamTimer -> return A.Int
            A.Timer A.RainTimer -> return A.Time
            _ -> diePC m $ formatCode "Expected timer; found %" t
  where
    m = findMeta tim

-- | Return the list of types carried by a protocol.
-- For a variant protocol, the second argument should be 'Just' the tag.
-- For a non-variant protocol, the second argument should be 'Nothing'.
protocolTypes :: Meta -> A.Type -> Maybe A.Name -> PassM [A.Type]
protocolTypes m t tag
    = case t of
        -- A user-defined protocol.
        A.UserProtocol n ->
           do st <- specTypeOfName n
              case (st, tag) of
                -- A simple protocol.
                (A.Protocol _ ts, Nothing) -> return ts
                (A.Protocol _ _, Just tagName) ->
                  diePC m $ formatCode "Tag % specified for non-variant protocol %" tagName n
                -- A variant protocol.
                (A.ProtocolCase _ ntss, Just tagName) ->
                  case lookup tagName ntss of
                    Just ts -> return ts
                    Nothing -> diePC m $ formatCode "Tag % not found in protocol %; expected one of %" tagName n (map fst ntss)
                (A.ProtocolCase _ ntss, Nothing) ->
                  diePC m $ formatCode "No tag specified for variant protocol %; expected one of %" n (map fst ntss)
                -- Not actually a protocol.
                _ -> diePC m $ formatCode "% is not a protocol" n
        -- Not a protocol (e.g. CHAN INT); just return it.
        _ -> return [t]

-- | Check a protocol communication.
-- Figure out the types of the items that should be involved in a protocol
-- communication, and run the supplied check against each item with its type.
checkProtocol :: Meta -> A.Type -> Maybe A.Name
                 -> [t] -> (A.Type -> t -> PassM ()) -> PassM ()
checkProtocol m t tag items doItem
    =  do its <- protocolTypes m t tag
          when (length its /= length items) $
            dieP m $ "Wrong number of items in protocol communication; found "
                     ++ (show $ length items) ++ ", expected "
                     ++ (show $ length its)
          sequence_ [doItem it item
                     | (it, item) <- zip its items]

-- | Check an 'ExpressionList' matches a set of types.
checkExpressionList :: [A.Type] -> A.ExpressionList -> PassM ()
checkExpressionList ets el
    = case el of
        A.FunctionCallList m n es ->
           do rs <- checkFunctionCall m n es
              when (length ets /= length rs) $
                diePC m $ formatCode ("Function % has wrong number of return values; found " ++ (show $ length rs) ++ ", expected " ++ (show $ length ets)) n
              sequence_ [checkType m et rt
                         | (et, rt) <- zip ets rs]
        A.IntrinsicFunctionCallList m n es ->
           do rs <- checkIntrinsicFunctionCall True m n es
              when (length ets /= length rs) $
                dieP m $ "Intrinsic function " ++ n ++ " has wrong number of return values; found " ++ (show $ length rs) ++ ", expected " ++ (show $ length ets)
              sequence_ [checkType m et rt
                         | (et, rt) <- zip ets rs]
        A.ExpressionList m es ->
           do when (length ets /= length es) $
                dieP m $ "Wrong number of items in expression list; found "
                         ++ (show $ length es) ++ ", expected "
                         ++ (show $ length ets)
              sequence_ [do rt <- astTypeOf e
                            checkType (findMeta e) et rt
                         | (e, et) <- zip es ets]
        A.AllocChannelBundle m n
              -> case ets of
                   [A.ChanDataType A.DirInput shA nA
                     ,A.ChanDataType A.DirOutput shB nB]
                     | A.nameName nA == A.nameName nB && A.nameName nA == A.nameName n
                     -> return ()
                   [A.ChanDataType A.DirOutput shA nA
                     ,A.ChanDataType A.DirInput shB nB]
                     | A.nameName nA == A.nameName nB && A.nameName nA == A.nameName n
                     -> return ()
                   _ -> dieP m $ "Wrong number of arguments, mismatched directions, or mismatched bundle types"


-- | Check a set of names are distinct.
checkNamesDistinct :: Meta -> [A.Name] -> PassM ()
checkNamesDistinct m ns
    = when (dupes /= []) $
        diePC m $ formatCode "List contains duplicate names: %" dupes
  where
    dupes :: [A.Name]
    dupes = nub (ns \\ nub ns)

-- | Check a 'Structured', applying the given check to each item found inside
-- it. This assumes that processes and specifications will be checked
-- elsewhere.
checkStructured :: Data t => Check t -> Check (A.Structured t)
checkStructured doInner s = transformOnly checkInner s >> return ()
  where
    checkInner m v
      =  do doInner v
            return $ A.Only m v

--}}}
--{{{  retyping checks

-- | Check that one type can be retyped to another.
checkRetypes :: Meta -> A.Type -> A.Type -> PassM ()
checkRetypes m fromT toT
    =  do (fromBI, fromN) <- evalBytesInType fromT
          (toBI, toN) <- evalBytesInType toT
          case (fromBI, toBI, fromN, toN) of
            (_, BIManyFree, _, _) ->
              dieP m "Multiple free dimensions in retype destination type"
            (BIJust _, BIJust _, Just a, Just b) ->
              when (a /= b) $
                dieP m "Sizes do not match in retype"
            (BIJust _, BIOneFree _ _, Just a, Just b) ->
              when (not ((b <= a) && (a `mod` b == 0))) $
                dieP m "Sizes do not match in retype"
            (BIOneFree _ _, BIJust _, Just a, Just b) ->
              when (not ((a <= b) && (b `mod` a == 0))) $
                dieP m "Sizes do not match in retype"
            -- Otherwise we must do a runtime check.
            _ -> return ()

-- | Evaluate 'BytesIn' for a type.
-- If the size isn't known at compile type, return 'Nothing'.
evalBytesInType :: A.Type -> PassM (BytesInResult, Maybe Int)
evalBytesInType t
    =  do bi <- bytesInType t
          n <- case bi of
                 BIJust e -> foldEval e
                 BIOneFree e _ -> foldEval e
                 _ -> return Nothing
          return (bi, n)
  where
    foldEval :: A.Expression -> PassM (Maybe Int)
    foldEval e
        =  do (e', isConst, _) <- constantFold e
              if isConst
                then evalIntExpression e' >>* Just
                else return Nothing

--}}}
--{{{  type context management

-- | Run an operation in a given type context.
inTypeContext :: Maybe A.Type -> PassM a -> PassM a
inTypeContext ctx body
    =  do pushTypeContext (case ctx of
                             Just A.Infer -> Nothing
                             _ -> ctx)
          v <- body
          popTypeContext
          return v

-- | Run an operation in the type context 'Nothing'.
noTypeContext :: PassM a -> PassM a
noTypeContext = inTypeContext Nothing

-- | Run an operation in the type context that results from subscripting
-- the current type context.
-- If the current type context is 'Nothing', the resulting one will be too.
inSubscriptedContext :: Meta -> PassM a -> PassM a
inSubscriptedContext m body
    =  do ctx <- getTypeContext
          subCtx <- case ctx of
                      Just t@(A.Array _ _) ->
                        trivialSubscriptType m t >>* Just
                      Just t -> diePC m $ formatCode "Attempting to subscript non-array type %" t
                      Nothing -> return Nothing
          inTypeContext subCtx body

--}}}

addDirections :: Pass
addDirections = occamOnlyPass "Add direction specifiers to inputs and outputs"
  [] []
  (applyDepthM2 doProcess doAlternative)
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

scrubMobile :: PassM a -> PassM a
scrubMobile m
  = do ctx <- getTypeContext
       case ctx of
         (Just (A.Mobile t)) -> inTypeContext (Just t) m
         _ -> m

inferAllocMobile :: Meta -> A.Type -> A.Expression -> PassM A.Expression
inferAllocMobile m (A.Mobile {}) e
  = do t <- astTypeOf e >>= underlyingType m
       case t of
         A.Mobile {} -> return e
         _ -> return $ A.AllocMobile m (A.Mobile t) (Just e)
inferAllocMobile _ _ e = return e

--{{{  inferTypes

-- I can't put this in the where clause of inferTypes, so it has to be out
-- here.  It should be the type of ops inside the inferTypes function below.
type InferTypeOps
  = BaseOp
    `ExtOpMP` A.Expression
    `ExtOpMP` A.Dimension
    `ExtOpMP` A.Subscript
    `ExtOpMP` A.Replicator
    `ExtOpMP` A.Alternative
    `ExtOpMP` A.InputMode
    `ExtOpMP` A.Specification
    `ExtOpMP` A.Process
    `ExtOpMP` A.Variable

-- | Infer types.
inferTypes :: Pass A.AST
inferTypes = occamOnlyPass "Infer types"
  []
  [Prop.inferredTypesRecorded]
  recurse
  where
    ops :: InferTypeOps
    ops = baseOp
          `extOp` doExpression
          `extOp` doDimension
          `extOp` doSubscript
          `extOp` doArrayConstr
          `extOp` doReplicator
          `extOp` doAlternative
          `extOp` doInputMode
          `extOp` doSpecification
          `extOp` doProcess
          `extOp` doVariable

    descend :: DescendM PassM InferTypeOps
    descend = makeDescendM ops

    doExpression :: Transform A.Expression
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
              do ctx <- getTypeContext >>= (T.sequence . fmap (underlyingType m))
                 v' <- recurse v
                 t <- astTypeOf v' >>= underlyingType m
                 case (ctx, t) of
                   (Just (A.Mobile {}), A.Mobile {}) -> return $ A.ExprVariable m v'
                   (Just _, A.Mobile {}) -> return $ A.ExprVariable m
                     $ A.DerefVariable m v'
                   _ -> return $ A.ExprVariable m v'
            -- Other expressions don't modify the type context.
            _ -> descend outer

    doFunctionCall :: Meta -> Transform (A.Name, [A.Expression])
    doFunctionCall m (n, es) = do
      if isOperator (A.nameName n)
        then
              -- for operators, resolve the function name, based on the type
           do let opDescrip = "\"" ++ (A.nameName n) ++ "\" "
                    ++ case length es of
                         1 -> "unary"
                         2 -> "binary"
                         n -> show n ++ "-ary"

              es' <- noTypeContext $ mapM recurse es
              tes <- sequence [underlyingTypeOf m e `catchError` (const $ return A.Infer) | e <- es']
           
              cs <- getCompState

              resolvedOps <- sequence [ do ts' <- mapM (underlyingType m) ts
                                           return (op, n, ts')
                                      | (op, n, ts) <- csOperators cs
                                      ]
              
              -- The nubBy will ensure that only one definition remains for each
              -- set of type-arguments, and will keep the first definition in the
              -- list (which will be the most recent)
              possibles <- return
                [ ((opFuncName, es'), ts)
                | (raw, opFuncName, ts) <- nubBy opsMatch resolvedOps
                -- Must be right operator:
                , raw == A.nameName n
                -- Must be right arity:
                , length ts == length es
                -- Must have right types:
                , ts `typesEqForOp` tes
                ]
              case possibles of
                [] -> diePC m $ formatCode "No matching % operator definition found for types: %" opDescrip tes
                [poss] -> return $ fst poss
                posss -> dieP m $ "Ambigious " ++ opDescrip ++ " operator, matches definitions: "
                                ++ show (map (transformPair (A.nameMeta . fst) showOccam) posss)
        else
           do (_, fs) <- checkFunction m n
              doActuals m n fs direct es >>* (,) n
      where
        direct = error "Cannot direct channels passed to FUNCTIONs"

    doActuals :: Data a => Meta -> A.Name -> [A.Formal] -> Transform [a]
    doActuals m n fs as
        =  do checkActualCount m n fs as
              sequence [doActual m applyDir t a | (A.Formal _ t _, a) <- zip fs as]

    doActual :: Data a => Meta -> (Meta -> A.Direction -> Transform a) -> A.Type -> Transform a
    doActual m applyDir (A.ChanEnd dir _ _) a = recurse a >>= applyDir m dir
    doActual m _ t a = inTypeContext (Just t) $ recurse a
                        

    doDimension :: Transform A.Dimension
    doDimension dim = inTypeContext (Just A.Int) $ descend dim

    doSubscript :: Transform A.Subscript
    doSubscript s = inTypeContext (Just A.Int) $ descend s

    doExpressionList :: [A.Type] -> Transform A.ExpressionList
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

    doReplicator :: Transform A.Replicator
    doReplicator rep
        = case rep of
            A.For _ _ _ _ -> inTypeContext (Just A.Int) $ descend rep
            A.ForEach _ _ -> noTypeContext $ descend rep

    doAlternative :: Transform A.Alternative
    doAlternative (A.Alternative m pre v im p)
      = do pre' <- inTypeContext (Just A.Bool) $ recurse pre
           v' <- recurse v
           im' <- doInputMode v' im
           p' <- recurse p
           return $ A.Alternative m pre' v' im' p'
    doAlternative (A.AlternativeSkip m pre p)
      = do pre'  <- inTypeContext (Just A.Bool) $ recurse pre
           p' <- recurse p
           return $ A.AlternativeSkip m pre' p'

    doInputMode :: A.Variable -> Transform A.InputMode
    doInputMode v (A.InputSimple m iis)
      = do ts <- protocolItems m v >>* either id (const [])
           iis' <- sequence [inTypeContext (Just t) $ recurse ii
                            | (t, ii) <- zip ts iis]
           return $ A.InputSimple m iis'
    doInputMode v (A.InputCase m sv)
      = do ct <- astTypeOf v
           inTypeContext (Just ct) (recurse sv) >>* A.InputCase m
    doInputMode _ im = inTypeContext (Just A.Int) $ descend im

    doVariant :: Transform A.Variant
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
               Just ts -> do iis' <- sequence [inTypeContext (Just t) $ recurse ii
                                              | (t, ii) <- zip ts iis]
                             p' <- recurse p
                             return $ A.Variant m n iis' p'

    doStructured :: Data a => Transform (A.Structured a)
    doStructured (A.Spec mspec s@(A.Specification m n st) body)
        =  do (st', wrap) <- runReaderT (doSpecType n st) body
              -- Update the definition of each name after we handle it.
              modifyName n (\nd -> nd { A.ndSpecType = st' })
              wrap (recurse body) >>* A.Spec mspec (A.Specification m n st')
    doStructured s = descend s

    -- The second parameter is a modifier (wrapper) for the descent into the body
    doSpecType :: Data a => A.Name -> A.SpecType -> ReaderT (A.Structured a) PassM
      (A.SpecType, PassM (A.Structured a) -> PassM (A.Structured a))
    doSpecType n st
        = case st of
            A.Place _ _ -> lift $ inTypeContext (Just A.Int) $ descend st >>* addId
            A.Is m am t (A.ActualVariable v) ->
               do am' <- lift $ recurse am
                  t' <- lift $ recurse t
                  v' <- lift $ inTypeContext (Just t') $ recurse v
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
                    (A.ChanEnd dir _ _, _) -> do v'' <- lift $ makeEnd m dir v'
                                                 return (t', v'')
                    (A.Array _ (A.ChanEnd dir _ _), _) ->
                                         do v'' <- lift $ makeEnd m dir v'
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
                  return $ addId $ A.Is m am' t'' (A.ActualClaim v')
            A.Is m am t (A.ActualChannelArray vs) ->
               -- No expressions in this -- but we may need to infer the type
               -- of the variable if it's something like "cs IS [c]:".
               do t' <- lift $ recurse t
                  vs' <- lift $ mapM recurse vs >>= case t' of
                    A.Infer -> return
                    A.Array _ (A.Chan {}) -> return
                    A.Array _ (A.ChanEnd dir _ _) -> mapM (makeEnd m dir)
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
                      let before = modify $ \cs -> cs { csOperators = (raw, n, ts) : csOperators cs }
                          after = modify $ \cs -> cs { csOperators = tail (csOperators cs)}
                      return (func
                             ,\m -> do before
                                       x <- m
                                       after
                                       return x)
                    _ -> return func >>* addId
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
        doFuncDef :: [A.Type] -> Transform (A.Structured A.ExpressionList)
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

        findDir :: Data a => A.Name -> a -> PassM [A.Direction]
        findDir n = flip execStateT [] . makeRecurseM ops
          where
            ops = baseOp `extOpM` doVariable

            -- This will cover everything, since we will have inferred the direction
            -- specifiers before applying this function.
            doVariable :: A.Variable -> StateT [A.Direction] PassM A.Variable
            doVariable v@(A.DirectedVariable _ dir (A.Variable _ n')) | n == n'
              = modify (dir:) >> return v
            doVariable v = makeDescend ops v


    doProcess :: Transform A.Process
    doProcess p
        = case p of
            A.Assign m vs el ->
               do vs' <- noTypeContext $ recurse vs
                  ts <- mapM astTypeOf vs'
                  el' <- doExpressionList ts el
                  return $ A.Assign m vs' el'
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
               do fs <- checkProc m n
                  as' <- doActuals m n fs (\m dir (A.ActualVariable v) -> liftM
                    A.ActualVariable $ makeEnd m dir v) as
                  return $ A.ProcCall m n as'
            A.IntrinsicProcCall _ _ _ -> noTypeContext $ descend p
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
        isTagged :: A.Variable -> PassM Bool
        isTagged c
            =  do protoT <- checkChannel A.DirOutput c
                  case protoT of
                    A.UserProtocol n ->
                       do st <- specTypeOfName n
                          case st of
                            A.ProtocolCase _ _ -> return True
                            _ -> return False
                    _ -> return False

        doOutputItems :: Meta -> A.Variable -> Maybe A.Name
                         -> Transform [A.OutputItem]
        doOutputItems m v tag ois
            =  do chanT <- checkChannel A.DirOutput v
                  ts <- protocolTypes m chanT tag
                  sequence [doOutputItem t oi | (t, oi) <- zip ts ois]

        doOutputItem :: A.Type -> Transform A.OutputItem
        doOutputItem (A.Counted ct at) (A.OutCounted m ce ae)
            =  do ce' <- inTypeContext (Just ct) $ recurse ce
                  ae' <- inTypeContext (Just at) $ recurse ae
                  return $ A.OutCounted m ce' ae'
        doOutputItem A.Any o = noTypeContext $ recurse o
        doOutputItem t (A.OutExpression m e)
          = inTypeContext (Just t) (recurse e >>= inferAllocMobile m t)
              >>* A.OutExpression m

    doVariable :: Transform A.Variable
    doVariable (A.SubscriptedVariable m s v)
        =  do v' <- recurse v
              t <- astTypeOf v'
              underT <- resolveUserType m t
              s' <- recurse s >>= fixSubscript t
              v'' <- case underT of
                A.Mobile {} -> return $ A.DerefVariable m v'
                _ -> return v'
              return $ A.SubscriptedVariable m s' v''
    doVariable v
        =  do v' <- descend v
              ctx <- getTypeContext  >>= (T.sequence . fmap (underlyingType (findMeta v)))
              underT <- astTypeOf v' >>= resolveUserType (findMeta v)
              case (ctx, underT) of
                (Just (A.Mobile {}), A.Mobile {}) -> return v'
                (Just _, A.Mobile {}) -> return $ A.DerefVariable (findMeta v) v'
                _ -> return v'

    -- | Resolve the @v[s]@ ambiguity: this takes the type that @v@ is, and
    -- returns the correct 'Subscript'.
    fixSubscript :: A.Type -> A.Subscript -> PassM A.Subscript
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
    nameToUnscoped :: A.Name -> PassM A.Name
    nameToUnscoped n@(A.Name m _)
        =  do nd <- lookupName n
              findUnscopedName (A.Name m (A.ndOrigName nd))

    -- | Process a 'LiteralRepr', taking the type it's meant to represent or
    -- 'Infer', and returning the type it really is.
    doLiteral :: Transform (A.Type, A.LiteralRepr)
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

        doArrayElem :: A.Type -> A.Structured A.Expression -> PassM (A.Type, A.Structured A.Expression)
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
                          return (applyDimension dim wantT,
                                  A.Several m aes')
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
            doElems :: A.Type -> [A.Structured A.Expression] -> PassM (A.Type, [A.Structured A.Expression])
            doElems t aes
                =  do ts <- mapM (\ae -> doArrayElem t ae >>* fst) aes
                      let bestT = foldl betterType t ts
                      aes' <- mapM (\ae -> doArrayElem bestT ae >>* snd) aes
                      return (bestT, aes')
        -- An expression: descend into it with the right context.
        doArrayElem wantT (A.Only m e)
            =  do e' <- inTypeContext (Just wantT) $ doExpression e
                  t <- astTypeOf e'
                  checkType (findMeta e') wantT t
                  return (t, A.Only m e')

        -- | Turn a raw table literal into the appropriate combination of
        -- arrays and records.
        buildTable :: A.Type -> [A.Structured A.Expression] -> PassM A.LiteralRepr
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
            buildExpr :: A.Type -> A.Structured A.Expression -> PassM A.Expression
            buildExpr t (A.Several _ aes)
                =  do lr <- buildTable t aes
                      return $ A.Literal m t lr
            buildExpr _ (A.Only _ e) = return e

            buildElem :: A.Type -> A.Structured A.Expression -> PassM (A.Structured A.Expression)
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
--{{{  checkTypes

-- | Check the AST for type consistency.
-- This is actually a series of smaller passes that check particular types
-- inside the AST, but it doesn't really make sense to split it up.
checkTypes ::
 (PolyplateSpine t (OneOpQ (PassM ()) A.Variable) () (PassM ())
 ,PolyplateSpine t (OneOpQ (PassM ()) A.Expression) () (PassM ())
 ,PolyplateSpine t (OneOpQ (PassM ()) A.SpecType) () (PassM ())
 ,PolyplateSpine t (OneOpQ (PassM ()) A.Process) () (PassM ())
 ) => Pass t
checkTypes = occamOnlyPass "Check types"
  [Prop.inferredTypesRecorded, Prop.ambiguitiesResolved]
  [Prop.expressionTypesChecked, Prop.processTypesChecked,
    Prop.functionTypesChecked, Prop.retypesChecked]
  (\x -> do
    checkVariables x
    checkExpressions x
    checkSpecTypes x
    checkProcesses x
    return x
  )

--{{{  checkVariables

checkVariables :: PlainCheckOn A.Variable
checkVariables = checkDepthM doVariable
  where
    doVariable :: Check A.Variable
    doVariable (A.SubscriptedVariable m s v)
        =  do t <- astTypeOf v
              checkSubscript m s t
    doVariable (A.DirectedVariable m dir v)
        =  do t <- astTypeOf v >>= resolveUserType m
              case t of
                A.ChanEnd oldDir _ _ -> checkDir oldDir
                A.Chan _ _ -> ok
                A.Array _ (A.ChanEnd oldDir _ _) -> checkDir oldDir
                A.Array _ (A.Chan _ _) -> ok
                _ -> diePC m $ formatCode "Direction specified on non-channel variable of type: %" t
      where
        checkDir oldDir
            = if dir == oldDir
                then ok
                else dieP m "Direction specified does not match existing direction"
    doVariable (A.DerefVariable m v)
        =  do t <- astTypeOf v >>= resolveUserType m
              case t of
                A.Mobile _ -> ok
                _ -> diePC m $ formatCode "Dereference applied to non-mobile variable of type %" t
    doVariable _ = ok

--}}}
--{{{  checkExpressions

checkExpressions :: PlainCheckOn A.Expression
checkExpressions = checkDepthM doExpression
  where
    doExpression :: Check A.Expression
    doExpression (A.MostPos m t) = checkNumeric m t
    doExpression (A.MostNeg m t) = checkNumeric m t
    doExpression (A.SizeType m t) = checkSequence True m t
    doExpression (A.SizeExpr m e)
        =  do t <- astTypeOf e
              checkSequence True m t
    doExpression (A.Conversion m _ t e)
        =  do et <- astTypeOf e
              checkScalar m t >> checkScalar (findMeta e) et
    doExpression (A.Literal m t lr) = doLiteralRepr t lr
    doExpression (A.FunctionCall m n es)
        =  do rs <- checkFunctionCall m n es
              when (length rs /= 1) $
                diePC m $ formatCode "Function % used in an expression returns more than one value" n
    doExpression (A.IntrinsicFunctionCall m s es)
        = checkIntrinsicFunctionCall False m s es >> return ()
    doExpression (A.SubscriptedExpr m s e)
        =  do t <- astTypeOf e
              checkSubscript m s t
    doExpression (A.OffsetOf m rawT n)
        =  do t <- resolveUserType m rawT
              checkRecordField m t n
    doExpression (A.AllocMobile m t me) = checkAllocMobile m t me
    doExpression _ = ok

    doLiteralRepr :: A.Type -> A.LiteralRepr -> PassM ()
    doLiteralRepr t (A.ArrayListLiteral m aes)
        = doArrayElem m t aes
    doLiteralRepr t (A.RecordLiteral m es)
        =  do rfs <- resolveUserType m t >>= recordFields m
              when (length es /= length rfs) $
                dieP m $ "Record literal has wrong number of fields: found " ++ (show $ length es) ++ ", expected " ++ (show $ length rfs)
              sequence_ [checkExpressionType ft fe
                         | ((_, ft), fe) <- zip rfs es]
    doLiteralRepr _ _ = ok

    doArrayElem :: Meta -> A.Type -> A.Structured A.Expression -> PassM ()
    doArrayElem m t (A.Several _ aes)
        =  do checkArraySize m t (length aes)
              t' <- subscriptType (A.Subscript m A.NoCheck undefined) t
              sequence_ $ map (doArrayElem m t') aes
    doArrayElem _ t (A.Only _ e) = checkExpressionType t e
    doArrayElem m t (A.Spec _ (A.Specification _ _ (A.Rep _ (A.For _ _ count _))) body)
      = do t' <- subscriptType (A.Subscript m A.NoCheck undefined) t
           doArrayElem m t' body
--}}}
--{{{  checkSpecTypes

checkSpecTypes :: PlainCheckOn A.SpecType
checkSpecTypes = checkDepthM doSpecType
  where
    doSpecType :: Check A.SpecType
    doSpecType (A.Place _ e) = checkExpressionInt e
    doSpecType (A.Declaration _ _) = ok
    doSpecType (A.Is m am t (A.ActualVariable v))
        =  do tv <- astTypeOf v
              checkType (findMeta v) t tv
              checkRefAM m am
              amv <- abbrevModeOfVariable v
              checkAbbrev m amv am
    doSpecType (A.Is m am t (A.ActualExpression e))
        =  do te <- astTypeOf e
              checkType (findMeta e) t te
              checkValAM m am
              checkAbbrev m A.ValAbbrev am
    doSpecType (A.Is m am t (A.ActualClaim v))
        =  do tv <- astTypeOf v
              checkAbbrev m A.Abbrev am
              checkType (findMeta v) t tv
              case tv of
                A.ChanEnd _ A.Shared _ -> return ()
                A.ChanDataType _ A.Shared _ -> return ()
                _ -> dieP m "Expected shared channel end in claim"
    doSpecType (A.Is m am rawT (A.ActualChannelArray cs))
        =  do t <- resolveUserType m rawT
              checkAbbrev m A.Abbrev am
              let isChan (A.Chan {}) = True
                  isChan (A.ChanEnd {}) = True
                  isChan _ = False
              case t of
                A.Array [d] et | isChan et ->
                   do sequence_ [do rt <- astTypeOf c
                                    checkType (findMeta c) et rt
                                    am <- abbrevModeOfVariable c
                                    checkAbbrev m am A.Abbrev
                                 | c <- cs]
                      case d of
                        A.UnknownDimension -> ok
                        A.Dimension e ->
                           do v <- evalIntExpression e
                              when (v /= length cs) $
                                dieP m $ "Wrong number of elements in channel array abbreviation: found " ++ (show $ length cs) ++ ", expected " ++ show v
                _ -> dieP m "Expected 1D channel array type"
    doSpecType (A.DataType m t)
        = checkDataType m t
    doSpecType (A.ChanBundleType m _ fts)
       = when (null fts) $ dieP m "Channel bundles cannot be empty"
    doSpecType (A.RecordType m _ nts)
        =  do sequence_ [checkDataType (findMeta n) t
                         | (n, t) <- nts]
              checkNamesDistinct m (map fst nts)
    doSpecType (A.Protocol m ts)
        =  do when (length ts == 0) $
                dieP m "A protocol cannot be empty"
              mapM_ (checkCommunicable m) ts
    doSpecType (A.ProtocolCase m ntss)
        =  do sequence_ [mapM_ (checkCommunicable (findMeta n)) ts
                         | (n, ts) <- ntss]
              checkNamesDistinct m (map fst ntss)
    doSpecType (A.Proc m _ fs _)
        = sequence_ [when (am == A.Original) $ unexpectedAM m
                     | A.Formal am _ n <- fs]
    doSpecType (A.Function m _ rs fs (Just body))
        =  do when (length rs == 0) $
                dieP m "A function must have at least one return type"
              sequence_ [do when (am /= A.ValAbbrev) $
                              diePC (findMeta n) $ formatCode "Argument % is not a value abbreviation" n
                            checkDataType (findMeta n) t
                         | A.Formal am t n <- fs]
              -- FIXME: Run this test again after free name removal
              doFunctionBody rs body
      where
        doFunctionBody :: [A.Type]
                          -> Either (A.Structured A.ExpressionList) A.Process
                          -> PassM ()
        doFunctionBody rs (Left s) = checkStructured (checkExpressionList rs) s
        -- FIXME: Need to know the name of the function to do this
        doFunctionBody rs (Right p) = dieP m "Cannot check function process body"
    doSpecType (A.Function _ _ _ _ Nothing) = return ()
    doSpecType (A.Retypes m am t v)
        =  do fromT <- astTypeOf v
              checkRetypes m fromT t
              checkRefAM m am
              amv <- abbrevModeOfVariable v
              checkAbbrev m amv am
    doSpecType (A.RetypesExpr m am t e)
        =  do fromT <- astTypeOf e
              checkRetypes m fromT t
              checkValAM m am
              checkAbbrev m A.ValAbbrev am
    doSpecType (A.Rep _ (A.For _ start count step))
        =  do checkExpressionInt start
              checkExpressionInt count
              checkExpressionInt step
    doSpecType (A.Rep _ (A.ForEach _ e))
        =  do t <- astTypeOf e
              checkSequence False (findMeta e) t


    checkValAM :: Meta -> A.AbbrevMode -> PassM ()
    checkValAM m am
        = case am of
            A.ValAbbrev -> ok
            A.InitialAbbrev -> ok
            _ -> unexpectedAM m

    checkRefAM :: Meta -> A.AbbrevMode -> PassM ()
    checkRefAM m am
        = case am of
            A.Abbrev -> ok
            A.ResultAbbrev -> ok
            _ -> unexpectedAM m

    unexpectedAM :: Check Meta
    unexpectedAM m = dieP m "Unexpected abbreviation mode"

--}}}
--{{{  checkProcesses

checkProcesses :: PlainCheckOn A.Process
checkProcesses = checkDepthM doProcess
  where
    doProcess :: Check A.Process
    doProcess (A.Assign m vs el)
        -- We ignore dimensions here because we do the check at runtime.
        -- (That is, [2]INT := []INT is legal.)
        =  do vts <- sequence [astTypeOf v >>* removeFixedDimensions
                               | v <- vs]
              mapM_ checkWritable vs
              checkExpressionList vts el
    doProcess (A.Input _ v im) = doInput v im
    doProcess (A.Output m v ois) = doOutput m v ois
    doProcess (A.OutputCase m v tag ois) = doOutputCase m v tag ois
    doProcess (A.ClearMobile _ v)
        =  do t <- astTypeOf v
              case t of
                A.Mobile _ -> ok
                _ -> diePC (findMeta v) $ formatCode "Expected mobile type; found %" t
              checkWritable v
    doProcess (A.Skip _) = ok
    doProcess (A.Stop _) = ok
    doProcess (A.Seq _ s) = checkStructured (\p -> ok) s
    doProcess (A.If _ s) = checkStructured doChoice s
    doProcess (A.Case _ e s)
        =  do t <- astTypeOf e
              checkCaseable (findMeta e) t
              checkStructured (doOption t) s
    doProcess (A.While _ e _) = checkExpressionBool e
    doProcess (A.Par _ _ s) = checkStructured (\p -> ok) s
    doProcess (A.Processor _ e _) = checkExpressionInt e
    doProcess (A.Alt _ _ s) = checkStructured doAlternative s
    doProcess (A.ProcCall m n as)
        =  do fs <- checkProc m n
              checkActuals m n fs as
    doProcess (A.IntrinsicProcCall m n as)
        = case lookup n intrinsicProcs of
            Just args ->
              do let fs = [A.Formal am t (A.Name m s)
                           | (am, t, s) <- args]
                 checkActuals m (A.Name m n) fs as
            Nothing -> dieP m $ n ++ " is not an intrinsic procedure"

    doAlternative :: Check A.Alternative
    doAlternative (A.Alternative m e v im p)
        =  do checkExpressionBool e
              case im of
                A.InputTimerRead _ _ ->
                  dieP m $ "Timer read not permitted as alternative"
                _ -> doInput v im
    doAlternative (A.AlternativeSkip _ e _)
        = checkExpressionBool e

    doChoice :: Check A.Choice
    doChoice (A.Choice _ e _) = checkExpressionBool e

    doInput :: A.Variable -> A.InputMode -> PassM ()
    doInput c (A.InputSimple m iis)
        =  do t <- checkChannel A.DirInput c
              checkProtocol m t Nothing iis doInputItem
    doInput c (A.InputCase _ s)
        =  do t <- checkChannel A.DirInput c
              checkStructured (doVariant t) s
      where
        doVariant :: A.Type -> A.Variant -> PassM ()
        doVariant t (A.Variant m tag iis _)
            = checkProtocol m t (Just tag) iis doInputItem
    doInput c (A.InputTimerRead m ii)
        =  do t <- checkTimer c
              doInputItem t ii
    doInput c (A.InputTimerAfter m e)
        =  do t <- checkTimer c
              et <- astTypeOf e
              checkType (findMeta e) t et
    doInput c (A.InputTimerFor m e)
        =  do t <- checkTimer c
              et <- astTypeOf e
              checkType (findMeta e) t et

    doInputItem :: A.Type -> A.InputItem -> PassM ()
    doInputItem (A.Counted wantCT wantAT) (A.InCounted m cv av)
        =  do ct <- astTypeOf cv
              checkType (findMeta cv) wantCT ct
              checkWritable cv
              at <- astTypeOf av
              checkType (findMeta cv) wantAT at
              checkWritable av
    doInputItem t@(A.Counted _ _) (A.InVariable m v)
        = diePC m $ formatCode "Expected counted item of type %; found %" t v
    doInputItem wantT (A.InVariable _ v)
        =  do t <- astTypeOf v
              case wantT of
                A.Any -> checkCommunicable (findMeta v) t
                _ -> checkType (findMeta v) wantT t
              checkWritable v

    doOption :: A.Type -> A.Option -> PassM ()
    doOption et (A.Option _ es _)
        = sequence_ [do rt <- astTypeOf e
                        checkType (findMeta e) et rt
                     | e <- es]
    doOption _ (A.Else _ _) = ok

    doOutput :: Meta -> A.Variable -> [A.OutputItem] -> PassM ()
    doOutput m c ois
        =  do t <- checkChannel A.DirOutput c
              checkProtocol m t Nothing ois doOutputItem

    doOutputCase :: Meta -> A.Variable -> A.Name -> [A.OutputItem] -> PassM ()
    doOutputCase m c tag ois
        =  do t <- checkChannel A.DirOutput c
              checkProtocol m t (Just tag) ois doOutputItem

    doOutputItem :: A.Type -> A.OutputItem -> PassM ()
    doOutputItem (A.Counted wantCT wantAT) (A.OutCounted m ce ae)
        =  do ct <- astTypeOf ce
              checkType (findMeta ce) wantCT ct
              at <- astTypeOf ae
              checkType (findMeta ae) wantAT at
    doOutputItem t@(A.Counted _ _) (A.OutExpression m e)
        = diePC m $ formatCode "Expected counted item of type %; found %" t e
    doOutputItem wantT (A.OutExpression _ e)
        =  do t <- astTypeOf e
              case wantT of
                A.Any -> checkCommunicable (findMeta e) t
                _ -> checkType (findMeta e) wantT t

--}}}

--}}}
