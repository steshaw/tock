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

module RainTypes where

import TestUtil
import qualified AST as A
import Pass
import Data.Generics
import EvalConstants
import Errors
import Types
import Control.Monad.State
import CompState


-- | A pass that records inferred types.  Currently the only place where types are inferred is in seqeach\/pareach loops.
recordInfNameTypes :: Data t => t -> PassM t
recordInfNameTypes = everywhereM (mkM recordInfNameTypes')
  where
    recordInfNameTypes' :: A.Replicator -> PassM A.Replicator
    recordInfNameTypes' input@(A.ForEach m n e)
      = do arrType <- typeOfExpression e
           innerT <- case arrType of 
             A.Array (_:innerDims) t ->
               return $ case innerDims of 
                 [] -> t
                 _ -> A.Array innerDims t               
             _ -> dieP m "Cannot do a foreach loop over a non-array type (or array with zero dimensions)"
           defineName n A.NameDef {A.ndMeta = m, A.ndName = A.nameName n, A.ndOrigName = A.nameName n, 
                                   A.ndNameType = A.VariableName, A.ndType = (A.Declaration m innerT), 
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return input
    recordInfNameTypes' r = return r

everywhereASTM :: (Data s, Data t) => (s -> PassM s) -> t -> PassM t
everywhereASTM f = doGeneric `extM` (doSpecific f)
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric (everywhereASTM f)
    
    doSpecific :: Data t => (t -> PassM t) -> t -> PassM t
    doSpecific f x = (doGeneric x >>= f)

-- | Folds all constants.
constantFoldPass :: Data t => t -> PassM t
constantFoldPass = everywhereASTM doExpression
  where
    doExpression :: A.Expression -> PassM A.Expression
    doExpression = (liftM (\(x,_,_) -> x)) . constantFold

