{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

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

-- | Simplify communications.
module SimplifyComms where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import CompState
import Metadata
import Types
import Pass

simplifyComms :: A.Process -> PassM A.Process
simplifyComms = runPasses passes
  where
    passes =
      [ ("Define temporary variables for outputting expressions", outExprs)
      ]

outExprs :: Data t => t -> PassM t
outExprs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric outExprs

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Output m c ois)
        =  do (ois', specs) <- mapAndUnzipM changeItem ois
              let foldedSpec = foldl1 (.) specs
              return $ A.Seq m (foldedSpec $ A.OnlyP m $ A.Output m c ois')
    doProcess p = doGeneric p
  
    changeItem :: A.OutputItem -> PassM (A.OutputItem, A.Structured -> A.Structured)
    changeItem (A.OutExpression m e) = do (e', spec) <- transExpr m e
                                          return (A.OutExpression m e', spec)
    changeItem (A.OutCounted m ce ae) = do (ce', ceSpec) <- transExpr m ce
                                           (ae', aeSpec) <- transExpr m ae
                                           return (A.OutCounted m ce' ae', ceSpec . aeSpec)

    transExpr :: Meta -> A.Expression -> PassM (A.Expression, A.Structured -> A.Structured)
    -- If it's already an output direct from a variable, no need to change it:
    transExpr _ e@(A.ExprVariable {}) = return (e, id)
    transExpr m e = do (nm, spec) <- abbrevExpr m e
                       return (A.ExprVariable m $ A.Variable m nm, spec)
    
    abbrevExpr :: Meta -> A.Expression -> PassM (A.Name, A.Structured -> A.Structured)
    abbrevExpr m e = do t <- typeOfExpression e
                        specification@(A.Specification _ nm _) <- defineNonce m "output_var" (A.IsExpr m A.ValAbbrev t e) A.VariableName A.ValAbbrev
                        return (nm, A.Spec m specification)
