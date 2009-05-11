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

-- | The occam-specific frontend passes.
module OccamPasses (occamPasses, foldConstants, checkConstants, CheckConstantsOps) where
-- The ops are exported to make testing easier

import Control.Monad.State
import Data.Generics (Data)
import Data.List
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import System.IO

import qualified AST as A
import CompState
import Errors
import EvalConstants
import EvalLiterals
import GenerateC -- For nameString
import Metadata
import OccamCheckTypes
import OccamInferTypes
import Pass
import qualified Properties as Prop
import ShowCode
import Traversal
import Types
import Utils

-- | Occam-specific frontend passes.
occamPasses :: [Pass A.AST]
occamPasses =
    [ occamOnlyPass "Dummy occam pass" [] (Prop.agg_namesDone ++ [Prop.mainTagged]) return
    , addDirections
    , inferTypes
    , foldConstants
    , fixConstructorTypes
    , checkConstants
    , resolveAmbiguities
    , checkTypes
    , writeIncFile
    , pushUpDirections
    ]

writeIncFile :: Pass A.AST
writeIncFile = occamOnlyPass "Write .inc file" [] []
  (passOnlyOnAST "writeIncFile" (\t ->
    do out <- getCompOpts >>* csOutputIncFile
       case out of
         Just fn -> do f <- liftIO $ openFile fn WriteMode
                       (origLines, ns) <- runStateT (emitProcsAsExternal t) []
                       allLines <- mapM mask ns >>* (F.toList origLines ++)
                       liftIO $ hPutStr f $ unlines allLines
                       liftIO $ hClose f
         Nothing -> return ()
       return t
  ))
  where
    emitProcsAsExternal :: A.AST -> StateT [A.Name] PassM (Seq.Seq String)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n (A.Proc _ (A.PlainSpec,_) fs (Just _))) scope)
      = do origN <- lookupName n >>* A.ndOrigName
           thisProc <- sequence (
             [return $ "#PRAGMA TOCKEXTERNAL \"PROC " ++ origN ++ "("
             ] ++ intersperse (return ",") (map showFormal fs) ++
             [return $ ") = " ++ nameString n ++ "\""
             ]) >>* concat
           recTopLevelName n
           emitProcsAsExternal scope >>* (thisProc Seq.<|)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n (A.Function m (A.PlainSpec,_) ts fs (Just _))) scope)
      = do origN <- lookupName n >>* A.ndOrigName
           thisProc <- sequence (
             [return $ "#PRAGMA TOCKEXTERNAL \""
             ] ++ intersperse (return ",") (map (showType m) ts) ++
             [return $ " FUNCTION " ++ showFuncName origN ++ "("
             ] ++ intersperse (return ",") (map showFormal fs) ++
             [return $ ") = " ++ nameString n ++ "\""
             ]) >>* concat
           recTopLevelName n
           emitProcsAsExternal scope >>* (thisProc Seq.<|)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n
      (A.RecordType m ra nts)) scope)
      = do ts' <- mapM (underlyingType m) ts
           thisDef <- showCode $ A.Specification m n $ A.RecordType m ra (zip ns ts')
           recordType n
           recTopLevelName n
           emitProcsAsExternal scope >>* (thisDef Seq.<|)
      where
        (ns, ts) = unzip nts
    emitProcsAsExternal (A.Spec _ (A.Specification _ n
      (A.ChanBundleType m rm nts)) scope)
      = do ts' <- mapM (underlyingType m) ts
           thisDef <- showCode $ A.Specification m n $ A.ChanBundleType m rm (zip ns ts')
           recordType n
           recTopLevelName n
           emitProcsAsExternal scope >>* (thisDef Seq.<|)
      where
        (ns, ts) = unzip nts
    emitProcsAsExternal (A.Spec _ (A.Specification _ n
      (A.Protocol m ts)) scope)
      = do ts' <- mapM (underlyingType m) ts
           thisDef <- showCode $ A.Specification m n $ A.Protocol m ts'
           recordType n
           recTopLevelName n
           emitProcsAsExternal scope >>* (thisDef Seq.<|)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n
      (A.ProtocolCase m nts)) scope)
      = do ts' <- mapM (mapM $ underlyingType m) ts
           thisDef <- showCode $ A.Specification m n $ A.ProtocolCase m (zip ns ts')
           recordType n
           recTopLevelName n
           emitProcsAsExternal scope >>* (thisDef Seq.<|)
      where
        (ns, ts) = unzip nts
    emitProcsAsExternal (A.Spec _ (A.Specification _ n _) scope)
      = emitProcsAsExternal scope
    emitProcsAsExternal (A.ProcThen _ _ scope) = emitProcsAsExternal scope
    emitProcsAsExternal (A.Only {}) = return Seq.empty
    emitProcsAsExternal (A.Several _ ss)
      = foldl (liftM2 (Seq.><)) (return Seq.empty) (map emitProcsAsExternal ss)

    -- FIXME: for all the types, we should also output the types that they depend
    -- on

    showFuncName :: String -> String
    showFuncName s | isOperator s = "\"" ++ doubleStars s ++ "\""
                   | otherwise = s
      where
        doubleStars cs = concat [if c == '*' then "**" else [c] | c <- cs]

    recordType :: A.Name -> StateT [A.Name] PassM ()
    recordType n = modify (n:)

    recTopLevelName :: A.Name -> StateT [A.Name] PassM ()
    recTopLevelName n = modifyCompState $ \cs -> cs { csOriginalTopLevelProcs =
             A.nameName n : csOriginalTopLevelProcs cs }

    mask :: A.Name -> PassM String
    mask n = lookupName n >>* A.ndOrigName >>* ("#PRAGMA TOCKUNSCOPE " ++)

    showType :: Meta -> A.Type -> StateT [A.Name] PassM String
    showType m = showCode <.< underlyingType m

    showFormal :: A.Formal -> StateT [A.Name] PassM String
    showFormal (A.Formal am t n) = do t' <- underlyingType (findMeta n) t
                                      showCode $ A.Formal am t' n

-- | Fixed the types of array constructors according to the replicator count
fixConstructorTypes :: PassOn A.Expression
fixConstructorTypes = occamOnlyPass "Fix the types of array constructors"
  [Prop.constantsFolded]
  [Prop.arrayConstructorTypesDone]
  (applyBottomUpM doExpression)
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.Literal m prevT lit@(A.ArrayListLiteral _ expr))
      = do dims <- getDims prevT
           t' <- doExpr [] dims expr
           return $ A.Literal m t' lit
      where
        getDims :: A.Type -> PassM [A.Dimension]
        getDims (A.Array ds _) = return ds
        getDims t@(A.UserDataType {}) = resolveUserType m t >>= getDims
        getDims t = dieP m $ "Cannot deduce dimensions of array constructor: " ++ show t

        innerType :: A.Type -> PassM A.Type
        innerType (A.Array _ t) = return t
        innerType t@(A.UserDataType {}) = resolveUserType m t >>= innerType
        innerType t = dieP m $ "Cannot deduce dimensions of array constructor: " ++ show t

        doExpr :: [A.Dimension] -> [A.Dimension] -> A.Structured A.Expression -> PassM A.Type
        doExpr prev (d:_) (A.Several m []) = innerType prevT >>* A.Array (prev ++ [d])
        doExpr prev (d:dims) (A.Several m ss@(s:_))
          = doExpr (prev ++ [d]) dims s
        doExpr prev _ (A.Only _ e)
          = astTypeOf e >>* addDimensions prev
        doExpr prev dims (A.ProcThen _ _ e) = doExpr prev dims e
        doExpr prev (_:dims) (A.Spec _ (A.Specification _ _ (A.Rep _ rep)) body)
          = doExpr (prev ++ [count]) (dims) body
          where
            count = A.Dimension $ countReplicator rep
        doExpr _ dims s = diePC (findMeta s) $ formatCode
          ("fixConstructorTypes found unexpected: %, " ++ show s) dims

    doExpression (A.AllocMobile m _ e@(Just (A.Literal _ t (A.ArrayListLiteral {}))))
       = return $ A.AllocMobile m (A.Mobile t) e
    doExpression e = return e

-- | Handle ambiguities in the occam syntax that the parser can't resolve.
resolveAmbiguities :: PassOn A.ExpressionList
resolveAmbiguities = occamOnlyPass "Resolve ambiguities"
  [Prop.inferredTypesRecorded]
  [Prop.ambiguitiesResolved]
  (applyBottomUpM doExpressionList)
  where
    doExpressionList :: Transform A.ExpressionList
    -- A single function call inside an ExpressionList is actually a
    -- FunctionCallList, since it can have multiple results.
    doExpressionList (A.ExpressionList _ [A.FunctionCall m n es])
        = return $ A.FunctionCallList m n es
    doExpressionList (A.ExpressionList _ [A.IntrinsicFunctionCall m n es])
        = return $ A.IntrinsicFunctionCallList m n es
    doExpressionList e = return e

-- | Fold constant expressions.
foldConstants :: PassOn2 A.Expression A.Specification
foldConstants = occamOnlyPass "Fold constants"
  [Prop.inferredTypesRecorded]
  [Prop.constantsFolded]
  (applyBottomUpM2 doExpression doSpecification)
  where
    -- Try to fold all expressions we encounter. Since we've recursed into the
    -- expression first, this'll also fold subexpressions of non-constant
    -- expressions.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do (e', _, _) <- constantFold e
              return e'

    -- After we're done folding a specification, update its definition.
    -- (Even if it isn't an expression itself, it might have others inside it,
    -- so we just update them all.)
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification spec@(A.Specification m n (A.RetypesExpr _ _ t _))
        = do e <- getConstantName n
             case e of
               Just e' ->
                 let newSpec = A.Is m A.ValAbbrev t (A.ActualExpression e') in
                 do modifyName n $ \nd -> nd { A.ndSpecType = newSpec }
                    return $ A.Specification m n newSpec
               Nothing -> return spec
    doSpecification s@(A.Specification _ n st)
        =  do modifyName n (\nd -> nd { A.ndSpecType = st })
              return s

type CheckConstantsOps = A.Type :-* A.Option :-* A.SpecType :-* BaseOpM

-- | Check that things that must be constant are.
checkConstants :: PassOnOps CheckConstantsOps
checkConstants = occamOnlyPass "Check mandatory constants"
  [Prop.constantsFolded, Prop.arrayConstructorTypesDone]
  [Prop.constantsChecked]
  recurse
  where
    ops :: CheckConstantsOps PassM
    ops = doType :-* doOption :-* doSpecType :-* baseOpM

    descend :: DescendM PassM CheckConstantsOps
    descend = makeDescendM ops
    recurse :: RecurseM PassM CheckConstantsOps
    recurse = makeRecurseM ops
    
    doType :: A.Type -> PassM A.Type
    -- Avoid checking that mobile dimensions are constant:
    doType t@(A.Mobile {}) = return t
    doType (A.Array ds t) = liftM2 A.Array (mapM doDimension ds) (recurse t)
    doType t = descend t
    
    -- Check array dimensions are constant.
    doDimension :: A.Dimension -> PassM A.Dimension
    doDimension d@(A.Dimension e)
        =  do when (not $ isConstant e) $
                diePC (findMeta e) $ formatCode "Array dimension must be constant: %" e
              return d
    doDimension A.UnknownDimension = return A.UnknownDimension

    -- Avoid checking that the destination sizes for RETYPES\/RESHAPES are constant
    doSpecType :: Transform A.SpecType
    doSpecType st@(A.Retypes _ _ _ v) = recurse v >> return st
    doSpecType st@(A.RetypesExpr _ _ _ e) = recurse e >> return st
    doSpecType st = descend st
    

    -- Check case options are constant.
    doOption :: A.Option -> PassM A.Option
    doOption o@(A.Option _ es _)
        =  do sequence_ [when (not $ isConstant e) $
                           diePC (findMeta e) $ formatCode "Case option must be constant: %" e
                         | e <- es]
              return o
    doOption o = descend o

-- | Turns things like cs[0]? into cs?[0], which helps later on in the usage checking
-- (as we can consider cs? a different array than cs!).
pushUpDirections :: PassOn A.Variable
pushUpDirections = occamOnlyPass "Push up direction specifiers on arrays"
  [] []
  (applyBottomUpM doVariable)
  where
    doVariable :: Transform A.Variable
    doVariable origV@(A.DirectedVariable m dir v)
      = do t <- astTypeOf v
           case (t, v) of
             (A.Array {}, _) -> return origV
             (_, A.SubscriptedVariable m sub v') ->
               return $ A.SubscriptedVariable m sub $ A.DirectedVariable m dir v'
             _ -> return origV
    doVariable v = return v
