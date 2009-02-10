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
module OccamPasses (occamPasses, foldConstants, checkConstants) where

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import System.IO

import qualified AST as A
import CompState
import EvalConstants
import EvalLiterals
import GenerateC -- For nameString
import Metadata
import OccamTypes
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

writeIncFile :: Pass
writeIncFile = occamOnlyPass "Write .inc file" [] []
  (passOnlyOnAST "writeIncFile" (\t ->
    do out <- getCompState >>* csOutputIncFile
       case out of
         Just fn -> do f <- liftIO $ openFile fn WriteMode
                       contents <- emitProcsAsExternal t >>* (unlines . F.toList)
                       liftIO $ hPutStr f contents
                       liftIO $ hClose f
         Nothing -> return ()
       return t
  ))
  where
    emitProcsAsExternal :: A.AST -> PassM (Seq.Seq String)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n (A.Proc _ _ fs (Just _))) scope)
      = do origN <- lookupName n >>* A.ndOrigName
           thisProc <- sequence (
             [return $ "#PRAGMA TOCKEXTERNAL \"PROC " ++ origN ++ "("
             ] ++ intersperse (return ",") (map showCode fs) ++
             [return $ ") = " ++ nameString n ++ "\""
             ]) >>* concat
           modify $ \cs -> cs { csOriginalTopLevelProcs =
             A.nameName n : csOriginalTopLevelProcs cs }
           emitProcsAsExternal scope >>* (thisProc Seq.<|)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n (A.Function _ _ ts fs (Just _))) scope)
      = do origN <- lookupName n >>* A.ndOrigName
           thisProc <- sequence (
             [return $ "#PRAGMA TOCKEXTERNAL \""
             ] ++ intersperse (return ",") (map showCode ts) ++
             [return $ " FUNCTION " ++ showFuncName origN ++ "("
             ] ++ intersperse (return ",") (map showCode fs) ++
             [return $ ") = " ++ nameString n ++ "\""
             ]) >>* concat
           modify $ \cs -> cs { csOriginalTopLevelProcs =
             A.nameName n : csOriginalTopLevelProcs cs }
           emitProcsAsExternal scope >>* (thisProc Seq.<|)
    emitProcsAsExternal (A.Spec _ (A.Specification _ n _) scope)
      = emitProcsAsExternal scope
    emitProcsAsExternal (A.ProcThen _ _ scope) = emitProcsAsExternal scope
    emitProcsAsExternal (A.Only {}) = return Seq.empty
    emitProcsAsExternal (A.Several _ ss)
      = foldl (liftM2 (Seq.><)) (return Seq.empty) (map emitProcsAsExternal ss)

    showFuncName :: String -> String
    showFuncName s | isOperator s = "\"" ++ doubleStars s ++ "\""
                   | otherwise = s
      where
        doubleStars cs = concat [if c == '*' then "**" else [c] | c <- cs]

-- | Fixed the types of array constructors according to the replicator count
fixConstructorTypes :: PassOn A.Expression
fixConstructorTypes = occamOnlyPass "Fix the types of array constructors"
  [Prop.constantsFolded]
  [Prop.arrayConstructorTypesDone]
  (applyBottomUpM doExpression)
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.Literal m prevT lit@(A.ArrayListLiteral _ expr))
      = do prevT' <- underlyingType m prevT
           t' <- doExpr [] (getDims prevT') expr
           return $ A.Literal m t' lit
      where
        getDims :: A.Type -> [A.Dimension]
        getDims (A.Array ds _) = ds
        getDims t = error $ "Cannot deduce dimensions of array constructor: " ++ show t

        innerType :: A.Type -> A.Type
        innerType (A.Array _ t) = t
        innerType t = error $ "Cannot deduce dimensions of array constructor: " ++ show t

        doExpr :: [A.Dimension] -> [A.Dimension] -> A.Structured A.Expression -> PassM A.Type
        doExpr prev (d:_) (A.Several m []) = return $ A.Array (prev ++ [d]) $ innerType prevT
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

-- | Check that things that must be constant are.
checkConstants :: PassOn2 A.Dimension A.Option
checkConstants = occamOnlyPass "Check mandatory constants"
  [Prop.constantsFolded, Prop.arrayConstructorTypesDone]
  [Prop.constantsChecked]
  (applyDepthM2 doDimension doOption)
  where
    ops = baseOp `extOp` doType `extOp` doOption

    descend, recurse :: Data a => a -> PassM a
    descend = makeDescend ops
    recurse = makeRecurse ops
    
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
    doDimension d = return d

    -- Check case options are constant.
    doOption :: A.Option -> PassM A.Option
    doOption o@(A.Option _ es _)
        =  do sequence_ [when (not $ isConstant e) $
                           diePC (findMeta e) $ formatCode "Case option must be constant: %" e
                         | e <- es]
              return o
    doOption o = return o

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
