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
module OccamPasses (occamPasses, foldConstants) where

import Data.Generics

import qualified AST as A
import CompState
import EvalConstants
import Pass
import qualified Properties as Prop

-- | Occam-specific frontend passes.
occamPasses :: [Pass]
occamPasses = makePassesDep' ((== FrontendOccam) . csFrontend)
    [ ("Fold constants", foldConstants,
       [],
       [Prop.constantsFolded])
    , ("Dummy occam pass", dummyOccamPass,
       [],
       Prop.agg_namesDone ++ [Prop.expressionTypesChecked,
                              Prop.inferredTypesRecorded, Prop.mainTagged,
                              Prop.processTypesChecked])
    ]

-- | Fold constant expressions.
foldConstants :: Data t => t -> PassM t
foldConstants = doGeneric `extM` doSpecification `extM` doExpression
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric foldConstants

    -- When an expression is abbreviated, try to fold it, and update its
    -- definition so that it can be used when folding later expressions.
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification s@(A.Specification m n (A.IsExpr m' am t e))
        =  do e' <- doExpression e
              let st' = A.IsExpr m' am t e'
              modifyName n (\nd -> nd { A.ndType = st' })
              return $ A.Specification m n st'
    doSpecification s = doGeneric s

    -- For all other expressions, just try to fold them.
    -- We recurse into the expression first so that we fold subexpressions of
    -- non-constant expressions too.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do e' <- doGeneric e
              (e'', _, _) <- constantFold e'
              return e''

-- | A dummy pass for things that haven't been separated out into passes yet.
dummyOccamPass :: Data t => t -> PassM t
dummyOccamPass = return

