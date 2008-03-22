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
module OccamPasses (occamPasses, foldConstants, checkConstants,
                    checkRetypes) where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import CompState
import Errors
import EvalConstants
import EvalLiterals
import Metadata
import OccamTypes
import Pass
import qualified Properties as Prop
import ShowCode
import Types

-- | Occam-specific frontend passes.
occamPasses :: [Pass]
occamPasses = makePassesDep' ((== FrontendOccam) . csFrontend)
    [ ("Fold constants", foldConstants,
       [],
       [Prop.constantsFolded])
    , ("Fix the types of array constructors", fixConstructorTypes,
       [Prop.constantsFolded],
       [Prop.arrayConstructorTypesDone])
    , ("Check mandatory constants", checkConstants,
       [Prop.constantsFolded, Prop.arrayConstructorTypesDone],
       [Prop.constantsChecked])
    , ("Check types", checkTypes,
       [],
       [Prop.expressionTypesChecked, Prop.processTypesChecked])
    , ("Check retyping", checkRetypes,
       [],
       [Prop.retypesChecked])
    , ("Dummy occam pass", dummyOccamPass,
       [],
       Prop.agg_namesDone ++ [Prop.expressionTypesChecked,
                              Prop.inferredTypesRecorded, Prop.mainTagged,
                              Prop.processTypesChecked])
    ]

-- | Fixed the types of array constructors according to the replicator count
fixConstructorTypes :: Data t => t -> PassM t
fixConstructorTypes = applyDepthM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.ExprConstr m (A.RepConstr m' _ rep expr))
      = do t <- typeOfExpression expr
           let count = countReplicator rep
               t' = A.Array [A.Dimension count] t
           return $ A.ExprConstr m $ A.RepConstr m' t' rep expr
    doExpression e = return e

-- | Fold constant expressions.
foldConstants :: Data t => t -> PassM t
foldConstants = applyDepthM2 doExpression doSpecification
  where
    -- Try to fold all expressions we encounter. Since we've recursed into the
    -- expression first, this'll also fold subexpressions of non-constant
    -- expressions.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do (e', _, _) <- constantFold e
              return e'

    -- When an expression is abbreviated, update its definition so that it can
    -- be used when folding later expressions.
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification s@(A.Specification _ n st@(A.IsExpr _ _ _ _))
        =  do modifyName n (\nd -> nd { A.ndType = st })
              return s
    doSpecification s = return s


-- | Check that things that must be constant are.
checkConstants :: Data t => t -> PassM t
checkConstants = applyDepthM2 doDimension doOption
  where
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

-- | Check that retyping is safe.
checkRetypes :: Data t => t -> PassM t
checkRetypes = applyDepthM doSpecType
  where
    doSpecType :: A.SpecType -> PassM A.SpecType
    doSpecType st@(A.Retypes m _ t v)
        =  do fromT <- typeOfVariable v
              checkRetypes m fromT t
              return st
    doSpecType st@(A.RetypesExpr m _ t e)
        =  do fromT <- typeOfExpression e
              checkRetypes m fromT t
              return st
    doSpecType st = return st

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

    evalBytesInType :: A.Type -> PassM (BytesInResult, Maybe Int)
    evalBytesInType t
        =  do bi <- bytesInType t
              n <- case bi of
                     BIJust e -> maybeEvalIntExpression e
                     BIOneFree e _ -> maybeEvalIntExpression e
                     _ -> return Nothing
              return (bi, n)

-- | A dummy pass for things that haven't been separated out into passes yet.
dummyOccamPass :: Data t => t -> PassM t
dummyOccamPass = return

