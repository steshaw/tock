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

import qualified AST as A
import CompState
import EvalConstants
import EvalLiterals
import Metadata
import OccamTypes
import Pass
import qualified Properties as Prop
import ShowCode
import Traversal
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
    , ("Infer types", astAndState inferTypes,
       [Prop.constantsFolded],
       [Prop.inferredTypesRecorded])
    , ("Check types", checkTypes,
       [Prop.inferredTypesRecorded],
       [Prop.expressionTypesChecked, Prop.processTypesChecked,
        Prop.functionTypesChecked, Prop.retypesChecked])
    , ("Dummy occam pass", dummyOccamPass,
       [],
       Prop.agg_namesDone ++ [Prop.mainTagged])
    ]
  where
    -- Apply a pass to both the AST and the state.
    astAndState :: (forall t. Data t => t -> PassM t) -> A.AST -> PassM A.AST
    astAndState p ast
        =  do ast' <- p ast
              get >>= p >>= put
              return ast'

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

    -- After we're done folding a specification, update its definition.
    -- (Even if it isn't an expression itself, it might have others inside it,
    -- so we just update them all.)
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification s@(A.Specification _ n st)
        =  do modifyName n (\nd -> nd { A.ndType = st })
              return s

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

-- | A dummy pass for things that haven't been separated out into passes yet.
dummyOccamPass :: Data t => t -> PassM t
dummyOccamPass = return

