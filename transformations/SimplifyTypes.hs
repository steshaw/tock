{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

-- | Simplify types in the AST.
module SimplifyTypes (
    simplifyTypes
  , resolveNamedTypes
  ) where

import Control.Monad.State
import qualified Data.Traversable as T

import qualified AST as A
import CompState
import Metadata
import Pass
import qualified Properties as Prop
import Traversal
import Types

simplifyTypes :: [Pass]
simplifyTypes
  = [ resolveNamedTypes
    ]

-- | Turn named data types into their underlying types.
resolveNamedTypes :: Pass
resolveNamedTypes
    = pass "Resolve user-defined types"
           (Prop.agg_namesDone
            ++ [Prop.expressionTypesChecked, Prop.processTypesChecked])
           [Prop.typesResolvedInAST, Prop.typesResolvedInState]
           (\t -> do get >>= resolve >>= resolve_csNames >>= put
                     resolve t)
  where
    -- Work-around for data types not being resolved:
    resolve_csNames :: Transform CompState
    resolve_csNames cs = do csNames' <- T.mapM resolve $ csNames cs
                            return $ cs { csNames = csNames' }
    
    resolve :: PassType
    resolve = applyDepthM doType
      where
        doType :: A.Type -> PassM A.Type
        doType t@(A.UserDataType _) = underlyingType emptyMeta t
        doType t = return t
