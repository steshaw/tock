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

-- | Utilities for metaprogramming.
module PregenUtils
  ( astTypes
  ) where

import Control.Monad.State
import Data.Generics
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import System.IO.Unsafe

import qualified AST as A
import Utils

type TypeMap = Map Int (String, DataBox)
type TypeMapM = State TypeMap

-- | Given a starting value, find all the types that could possibly be inside
-- it.
findTypesIn :: Data t => t -> TypeMap
findTypesIn start = execState (doType start) Map.empty
  where
    doType :: Data t => t -> TypeMapM ()
    doType x
        =  do map <- get
              when (not $ key `Map.member` map) $
                 do modify $ Map.insert key (reps, DataBox x)
                    when (isAlgType dtype) $
                      mapM_ doConstr $ dataTypeConstrs dtype
      where
        rep = typeOf x
        key = unsafePerformIO $ typeRepKey rep
        reps = show rep
        dtype = dataTypeOf x

        doConstr :: Constr -> TypeMapM ()
        doConstr ctr
            = sequence_ [doType x' | DataBox x' <- args]
          where
            args = gmapQ DataBox (asTypeOf (fromConstr ctr) x)

-- | Reduce a 'TypeMap' to only the types in a particular module.
filterModule :: String -> TypeMap -> TypeMap
filterModule prefix = Map.filter (((prefix ++ ".") `isPrefixOf`) . fst)

-- | Reduce a 'TypeMap' to a list of 'DataBox'es, sorted by name.
justBoxes :: TypeMap -> [DataBox]
justBoxes = map snd . sortBy cmp . Map.elems
  where
    cmp (l, _) (r, _) = compare l r

-- | Witnesses for all the types defined in the 'AST' module.
astTypes :: [DataBox]
astTypes = justBoxes $ filterModule "AST" $ findTypesIn (undefined :: A.AST)

