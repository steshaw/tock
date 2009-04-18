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
module OccamCheckTypes (checkTypes, checkFunction, checkProc, checkChannel, protocolTypes,
  checkType, checkActualCount) where
-- Only checkTypes is used in a pass, and OccamInferTypes uses the rest

import Control.Monad.State
import Data.Generics (Data)
import Data.List
import Data.Maybe

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

--{{{  checkTypes

-- | Check the AST for type consistency.
-- This is actually a series of smaller passes that check particular types
-- inside the AST, but it doesn't really make sense to split it up.
checkTypes ::
 (PolyplateM t (OneOpM PassM A.Variable) () PassM
 ,PolyplateM t (OneOpM PassM A.Expression) () PassM
 ,PolyplateM t (OneOpM PassM A.SpecType) () PassM
 ,PolyplateM t (OneOpM PassM A.Process) () PassM
 ,PolyplateM t () (OneOpM PassM A.Variable) PassM
 ,PolyplateM t () (OneOpM PassM A.Expression) PassM
 ,PolyplateM t () (OneOpM PassM A.SpecType) PassM
 ,PolyplateM t () (OneOpM PassM A.Process) PassM
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

checkVariables :: PassTypeOn A.Variable
checkVariables x = checkDepthM doVariable x >> return x
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
                A.ChanDataType oldDir _ _ -> checkDir oldDir
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

checkExpressions :: PassTypeOn A.Expression
checkExpressions x = checkDepthM doExpression x >> return x
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

checkSpecTypes :: PassTypeOn A.SpecType
checkSpecTypes x = checkDepthM doSpecType x >> return x
  where
    doSpecType :: Check A.SpecType
    doSpecType (A.Place _ e) = checkExpressionInt e
    doSpecType (A.Declaration _ _) = ok
    doSpecType (A.Forking _) = ok
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
              case tv of
                A.ChanEnd a A.Shared b ->
                  checkType (findMeta v) t (A.ChanEnd a A.Unshared b)
                A.ChanDataType a A.Shared b ->
                  checkType (findMeta v) t (A.ChanDataType a A.Unshared b)
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

checkProcesses :: PassTypeOn A.Process
checkProcesses x = checkDepthM doProcess x >> return x
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
    doProcess (A.Fork _ _ p) = doProcess p
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

-- For records, because of the way separate compilation works, the same record
-- might end up with two different names.  So we consider records to be the same
-- type, iff:
-- a. They have the same original name, AND
-- b. Their attributes are the same, AND
-- c. There are the same number of fields, AND
-- d. The fields have matching names, AND
-- e. The fields have matching types.
sameType (A.Record na) (A.Record nb)
  = do nad <- lookupName na
       nbd <- lookupName nb
       let matchOn :: Eq a => (A.NameDef -> a) -> Bool
           matchOn f = f nad == f nbd

           allButTypesSame = and $
             [matchOn A.ndOrigName
             ,matchOn $ (\(A.RecordType _ ra _) -> ra) . A.ndSpecType
             ,matchOn $ (\(A.RecordType _ _ fs) -> length fs) . A.ndSpecType
             ,matchOn $ (\(A.RecordType _ _ fs) -> map fst fs) . A.ndSpecType
             ]

           getTypes = (\(A.RecordType _ _ fs) -> map snd fs) . A.ndSpecType

       if allButTypesSame
         then liftM and $ mapM (uncurry sameType) (zip (getTypes nad) (getTypes nbd))
         else return False
-- For protocols (due to separate compilation) we check that the original names
-- were the same, and that all the types match, similar to records
sameType (A.UserProtocol na) (A.UserProtocol nb)
  = do nad <- lookupName na
       nbd <- lookupName nb
       if A.ndOrigName nad == A.ndOrigName nbd
         then case (A.ndSpecType nad, A.ndSpecType nbd) of
           (A.Protocol _ ats, A.Protocol _ bts)
             | length ats == length bts
               -> liftM and $ mapM (uncurry sameType) (zip ats bts)
           (A.ProtocolCase _ ants, A.ProtocolCase _ bnts)
             | length ants == length bnts && map fst ants == map fst bnts
               -> liftM and $ mapM (liftM and . sequence . uncurry (zipWith sameType)) (zip (map snd ants) (map snd bnts))
           _ -> return False
         else return False
-- Finally, for channel bundle types, we proceed as with the others:
sameType (A.ChanDataType dirA shA na) (A.ChanDataType dirB shB nb)
  | dirA == dirB && shA == shB
  = do nad <- lookupName na
       nbd <- lookupName nb
       if A.ndOrigName nad == A.ndOrigName nbd
         then case (A.ndSpecType nad, A.ndSpecType nbd) of
                (A.ChanBundleType _ arm ants, A.ChanBundleType _ brm bnts)
                  | arm == brm && length ants == length bnts && map fst ants == map fst bnts
                    -> liftM and $ mapM (uncurry sameType) (zip (map snd ants) (map snd bnts))
                _ -> return False
         else return False
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
 = do et' <- resolveUserType m et
      rt' <- resolveUserType m rt
      case (et', rt') of
        (A.Infer, _) -> ok
        (A.Array ds t, A.Array ds' t') ->
          do valid <- areValidDimensions ds ds'
             if valid
               then checkType m t t'
               else bad
        (A.Mobile t, A.Mobile t') -> checkType m t t'
        _ ->
          do same <- sameType rt' et'
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

-- | Check the type of an expression.
checkExpressionType :: A.Type -> A.Expression -> PassM ()
checkExpressionType et e = astTypeOf e >>= checkType (findMeta e) et

-- | Check that an expression is of integer type.
checkExpressionInt :: Check A.Expression
checkExpressionInt e = checkExpressionType A.Int e

-- | Check that an expression is of boolean type.
checkExpressionBool :: Check A.Expression
checkExpressionBool e = checkExpressionType A.Bool e

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
               do case (innerT, me) of
                    -- Array dimensions must be known if there's no initialiser.
                    -- If there is an initialiser, we'll get the dimensions from
                    -- that.
                    (A.Array ds _, Nothing) -> mapM_ (checkFullDimension m) ds
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
