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
-- TODO add an error return
flowAlgorithm :: (Ord n, Eq a) => GraphFuncs n e a -> [n] -> n -> Map.Map n a
flowAlgorithm funcs nodes startNode
  = iterate
      (Set.fromList nonStartNodes)
      (Map.fromList $ (startNode,initVal funcs):(zip nonStartNodes (repeat (defVal funcs))))
  where
    nonStartNodes = (filter ((/=) startNode) nodes)
    
    foldWithMaybe :: (b -> Maybe a -> a) -> Maybe a -> [b] -> a
    foldWithMaybe _ Nothing [] = error "empty list for previous nodes in flowAlgorithm" -- TODO use a better error return
    foldWithMaybe _ (Just a) [] = a
    foldWithMaybe f ma (b:bs) = foldWithMaybe f (Just $ f b ma) bs
    
  
    -- TODO stop using fromJust, in favour of adding a more obvious error (even though fromJust should be safe here)
--    iterate :: Ord n => Set.Set n -> Map.Map n a -> Map.Map n a
    iterate workList vals
      | Set.null workList = vals
      | otherwise
          = let (node, workList') = Set.deleteFindMin workList in
            let total = foldWithMaybe (\ne -> nodeFunc funcs ne (fromJust $ Map.lookup (fst ne) vals)) Nothing (prevNodes funcs node) in
            if total /= fromJust (Map.lookup node vals)
              then iterate (workList' `Set.union` (Set.fromList $ map fst $ nextNodes funcs node)) (Map.insert node total vals)
              else iterate workList' vals
