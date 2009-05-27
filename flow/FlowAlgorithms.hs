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

import Utils

data GraphFuncs n e result = GF {
   -- (Node, Edge) -> current value for said node -> current aggregate effect for
   -- the current node -> new aggregate effect
   -- If it is the first node to be processed for this iteration, it will be
   -- given Nothing, otherwise the result is fed back when processing the next
   -- node.  The second parameter is from the last iteration.
   nodeFunc :: (n,e) -> result -> Maybe result -> result

   -- For forward data-flow, this should be the predecessor nodes.  For backward
   -- data-flow, this should be the successor nodes
   ,nodesToProcess :: n -> [(n,e)]

   -- For forward data-flow, this should be the successor nodes.  For backward
   -- data-flow, this should be the predecessor nodes
   ,nodesToReAdd :: n -> [(n,e)]

   -- defVal is the default starting value for all the nodes (except the first node)
   ,defVal :: result

   -- Used to give a helpful error message about a node
   ,userErrLabel :: n -> String
  }

-- Joins together two sets of GraphFuncs into one.  For nodesToProcess, nodesToReAdd
-- and userErrLabel it takes the functions from the first argument.  The first
-- two should be identical to that for the second argument.  This is only common
-- sense; if you try to combine a forward flow algorithm with a backwards flow
-- algorithm, it's not going to work!
joinGraphFuncs :: GraphFuncs n e resultA -> GraphFuncs n e resultB -> GraphFuncs
  n e (resultA, resultB)
joinGraphFuncs gfA gfB
  = GF { nodeFunc = \ne (rA, rB) mrAB ->
           (nodeFunc gfA ne rA (fmap fst mrAB)
           ,nodeFunc gfB ne rB (fmap snd mrAB)
           )
       , nodesToProcess = nodesToProcess gfA
       , nodesToReAdd = nodesToReAdd gfB
       , defVal = (defVal gfA, defVal gfB)
       , userErrLabel = userErrLabel gfA
       }

-- | Given the graph functions, a list of nodes and an entry node, performs
-- an iterative data-flow analysis.  All the nodes in the list should be connected to
-- the starting node, and there should be no nodes without nodes to process
-- (i.e. where nodesToProcess returns the empty list) in the list except the
-- starting node.
--
-- The implication of the above is that you should /not/ pass as the second
-- parameter all the nodes in the graph (unless you /know/ that it is fully
-- connected).  Instead you should pass the connected nodes.  If you are doing
-- forward data flow (using @nodesToProcess = lpre graph@), you can find the connected
-- nodes using @(dfs [initNode] graph)@.  If you are doing backward data flow
-- (using @nodesToProcess = lsuc graph@), you can find the connected nodes using
-- @(rdfs [initNode] graph)@.
--
-- The general idea of iterative data-flow is that all nodes start out with
-- a default "guessed" value.  Then each node is processed in turn by using
-- an accumulating value (to start with Nothing), and the values associated with
-- each of the nodesToProcess in the graph.  This algorithm is performed repeatedly,
-- processing all nodes, and if a node changes its value, re-adding all its
-- nodes in the other direction (nodesToReAdd) to the worklist to be processed again.
--
-- The function is agnostic as to the representation of the graph, provided
-- it supports the two required operations (nodesToProcess and nodesToReAdd).
--  It can also do forward or backward data flow by just swapping those two
-- functions over.
flowAlgorithm :: forall n e result. (Ord n, Show n, Eq result) =>
  GraphFuncs n e result -- ^ The set of functions to handle the graph.
  -> [n] -- ^ The list of all nodes to process
  -> (n, result) -- ^ The starting node (can also be in the list) and its
                 -- starting guess
  -> Either String (Map.Map n result) -- ^ Either an error or the map from
                                      -- nodes to results
flowAlgorithm funcs nodes (startNode, startVal)
  = iterate
      nonStartNodesSet
      (Map.fromList $ (startNode, startVal):(zip nonStartNodes (repeat (defVal funcs))))
  where
    -- The nodes list, with the start node removed:
    nonStartNodes :: [n]
    nonStartNodes = (filter ((/=) startNode) nodes)

    nonStartNodesSet :: Set.Set n
    nonStartNodesSet = Set.fromList nonStartNodes

    allNodesSet :: Set.Set n
    allNodesSet = Set.singleton startNode `Set.union` nonStartNodesSet

    filtNodes :: [(n,e)] -> [(n,e)]
    filtNodes = filter ((`Set.member` allNodesSet) . fst)

    -- | Folds left, but with Either types involved.  Gives an error if there
    -- are no nodes in the given list at the start (i.e. when its second parameter
    -- is Left).  Otherwise feeds the aggregate result back round on each
    -- iteration of the list, but stops at the first error while folding (so
    -- a bit like foldM)
    foldWithEither ::
      (b -- ^ The list value being folded
       -> Maybe result
         -- ^ The current accumulated result.  Nothing if it is the first item
         -- in the list
       -> Either String result
         -- ^ Either give back an error or a new accumulated result
      )
      -> Either String result
            -- ^ The starting value should be (Left errorMessageForEmptyList)
            -- and thereafter it will be Right result.
      -> [b] -- ^ The list to fold over
      -> Either String result
            -- ^ Either an error or the result.  Errors can
            -- be caused by a starting empty list, or an error in processing
            -- an individual item
    foldWithEither _ (Left err) [] = throwError $ "empty list for previous nodes in flowAlgorithm:"
      ++ err
    foldWithEither _ (Right a) [] = return a
    foldWithEither f ea (b:bs)
      = do b' <- f b $ eitherToMaybe ea
           foldWithEither f (Right b') bs

    -- | Given a map from node to current results, a node and edge to process
    -- (the node is from nodesToProcess, and the edge connects it to the current
    -- node), an aggregate result (Nothing if nothing processed yet), returns
    -- an error or a new result by processing the node
    iterateNode :: Map.Map n result -> (n,e) -> Maybe result -> Either String result
    iterateNode vals ne ma
      = case Map.lookup (fst ne) vals of
          Nothing -> throwError $ "Value not found for node edge: " ++ show (fst ne)
          Just v -> return $ nodeFunc funcs ne v ma

    -- | Iterates the dataflow analysis.  It is given a set of nodes to process,
    -- a map from nodes to current results, and iterates until it gives back
    -- an error or the list of final results  
    iterate :: Set.Set n -> Map.Map n result -> Either String (Map.Map n result)
    iterate workList vals
      -- No nodes left to process, finished:
      | Set.null workList = Right vals
      | otherwise
               -- Pick the next node from the list and remove it:
          = do let (node, workList') = Set.deleteFindMin workList
               -- Process that node:
               total <- foldWithEither (iterateNode vals) (Left $
                 "Nodes still to process: " ++ show workList
                 ++ " " ++ userErrLabel funcs node)
                 (filtNodes $ nodesToProcess funcs node)
               nodeVal <- case Map.lookup node vals of
                 Nothing -> throwError "Could not find node during flowAlgorithm"
                 Just x -> return x
               if total /= nodeVal
                 -- If the value has changed, that will cascade to affect all
                 -- its dependents, so add all
                 -- of them back to the work list:
                 then iterate (workList' `Set.union` (Set.fromList $
                   map fst $ filtNodes $ nodesToReAdd funcs node)) (Map.insert node total vals)
                 -- If the value hasn't changed, forget it and go on to the
                 -- next one:
                 else iterate workList' vals
