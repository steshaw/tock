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

module FlowAlgorithms where

import Control.Monad.Error
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

data GraphFuncs n e a = GF {
   -- (Node, Edge) -> previous assumed input -> current aggregate effect -> new aggregate effect
   nodeFunc :: (n,e) -> a -> Maybe a -> a
   ,prevNodes :: n -> [(n,e)]
   ,nextNodes :: n -> [(n,e)]
   ,initVal :: a
   -- defVal should be the unit of the aggregation.  That is, if (nodeFunc a b) == defVal, then (nodeFunc a b defVal) == defVal too
   -- TODO not sure if the above is still true
   ,defVal :: a
  }

-- TODO further in the future, consider making this work nicely with the inductive graph rather than using node lists

-- | Given the graph functions, a list of nodes and an entry node, performs
-- an iterative data-flow analysis.
flowAlgorithm :: forall n e a. (Ord n, Show n, Eq a) => GraphFuncs n e a -> [n] -> n -> Either String (Map.Map n a)
flowAlgorithm funcs nodes startNode
  = iterate
      (Set.fromList nonStartNodes)
      (Map.fromList $ (startNode,initVal funcs):(zip nonStartNodes (repeat (defVal funcs))))
  where
    nonStartNodes = (filter ((/=) startNode) nodes)
    
    foldWithMaybe :: (b -> Maybe a -> Either String a) -> Maybe a -> [b] -> Either String a
    foldWithMaybe _ Nothing [] = throwError "empty list for previous nodes in flowAlgorithm"
    foldWithMaybe _ (Just a) [] = return a
    foldWithMaybe f ma (b:bs)
      = do b' <- f b ma
           foldWithMaybe f (Just b') bs

    iterateNode :: Map.Map n a -> (n,e) -> Maybe a -> Either String a
    iterateNode vals ne ma
      = case Map.lookup (fst ne) vals of
          Nothing -> throwError $ "Value not found for node edge: " ++ show (fst ne)
          Just v -> return $ nodeFunc funcs ne v ma
  
    iterate :: Set.Set n -> Map.Map n a -> Either String (Map.Map n a)
    iterate workList vals
      | Set.null workList = Right vals
      | otherwise
          = do let (node, workList') = Set.deleteFindMin workList
               total <- foldWithMaybe (iterateNode vals) Nothing (prevNodes funcs node)
               nodeVal <- Map.lookup node vals
               if total /= nodeVal
                 then iterate (workList' `Set.union` (Set.fromList $ map fst $ nextNodes funcs node)) (Map.insert node total vals)
                 else iterate workList' vals
