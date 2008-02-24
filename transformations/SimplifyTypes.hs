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

-- | Simplify types in the AST.
module SimplifyTypes (simplifyTypes) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map

import qualified AST as A
import CompState
import Metadata
import Pass
import qualified Properties as Prop
import Types

simplifyTypes :: [Pass]
simplifyTypes = makePassesDep
      [ ("Resolve types in AST", resolveNamedTypes, Prop.agg_namesDone, [Prop.typesResolvedInAST])
      , ("Resolve types in state", rntState, Prop.agg_namesDone, [Prop.typesResolvedInState])
      ]

-- | Turn named data types into their underlying types.
resolveNamedTypes :: Data t => t -> PassM t
resolveNamedTypes = doGeneric `extM` doType
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric resolveNamedTypes

    doType :: A.Type -> PassM A.Type
    doType t@(A.UserDataType _) = underlyingType emptyMeta t
    doType t = doGeneric t

-- | Resolve named types in CompState.
rntState :: Data t => t -> PassM t
rntState p = (get >>= nullBodies >>= resolveNamedTypes >>= put) >> return p
  where
    nullBodies :: CompState -> PassM CompState
    nullBodies st = return $ st {csNames = Map.map nullProcFuncDefs (csNames st)}
    
    nullProcFuncDefs :: A.NameDef -> A.NameDef
    nullProcFuncDefs (A.NameDef m n on nt (A.Proc m' sm fs _) am pl) = (A.NameDef m n on nt (A.Proc m' sm fs (A.Skip m')) am pl)
    nullProcFuncDefs (A.NameDef m n on nt (A.Function m' sm ts fs (Left _)) am pl) = (A.NameDef m n on nt (A.Function m' sm ts fs (Left $ A.Several m' [])) am pl)
    nullProcFuncDefs (A.NameDef m n on nt (A.Function m' sm ts fs (Right _)) am pl) = (A.NameDef m n on nt (A.Function m' sm ts fs (Right $ A.Skip m')) am pl)
    nullProcFuncDefs x = x

