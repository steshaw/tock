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

module ImplicitMobility (implicitMobility) where

import Control.Monad
import Control.Monad.Trans
import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import Errors
import FlowAlgorithms
import FlowGraph
import FlowUtils
import Metadata
import Pass
import UsageCheckUtils
import Utils

-- | Calculates a map from each node to a set of variables that will be
-- used again afterwards.  Used in this context means it can possibly be
-- read from before being written to
calculateUsedAgainAfter :: Monad m => FlowGraph m UsageLabel -> Node -> Either String (Map.Map Node
 (Set.Set Var))
calculateUsedAgainAfter g startNode
  = flowAlgorithm funcs (udfs [startNode] g) (startNode, Set.empty)
  where
    funcs :: GraphFuncs Node EdgeLabel (Set.Set Var)
    funcs = GF     
      { nodeFunc = iterate
      -- Backwards data flow:
      , nodesToProcess = lsuc g
      , nodesToReAdd = lpre g
      , defVal = Set.empty
      , userErrLabel = ("for node at: " ++) . show . fmap getNodeMeta . lab g
      }

    iterate :: (Node, EdgeLabel) -> Set.Set Var -> Maybe (Set.Set Var) -> Set.Set
      Var
    iterate node prevVars maybeVars = case lab g (fst node) of
      Just ul ->
        let vs = nodeVars $ getNodeData ul
            readFromVars = readVars vs
            writtenToVars = writtenVars vs
            addTo = fromMaybe prevVars maybeVars
        in (readFromVars `Set.union` addTo) `Set.difference` writtenToVars
      Nothing -> error "Node label not found in calculateUsedAgainAfter"

--TODO rememember to take note of declarations/scope, otherwise this:
-- seqeach (..) {int:x; ... x = 3;}
-- will look like x is used again on the next loop iteration

-- TODO look at the types, too!
printMoveCopyDecisions :: Monad m => FlowGraph m UsageLabel -> [Node] -> PassM ()
printMoveCopyDecisions gr ns
  = do decs <- makeMoveCopyDecisions gr ns
       mapM_ printDec $ Map.toList decs
  where
    printDec :: ((Node, Var), Decision) -> PassM ()
    printDec ((_,v), dec) = liftIO $ putStrLn $
      show (findMeta v) ++ show v ++ " " ++ show dec

data Decision = Move | Copy deriving (Show, Ord, Eq)

makeMoveCopyDecisions :: Monad m => FlowGraph m UsageLabel -> [Node] ->
  PassM (Map.Map (Node, Var) Decision)
makeMoveCopyDecisions gr
  = foldM processConnected (Map.empty)
  where
    -- Processes the entire sub-graph that is connected to the given node
    processConnected :: Map.Map (Node, Var) Decision -> Node ->
      PassM (Map.Map (Node, Var) Decision)
    processConnected m n = case calculateUsedAgainAfter gr n of
      Left err -> dieP (getNodeMeta $ fromJust $ lab gr n) err
      Right mvs -> foldM (processNode mvs) m $ Map.keys mvs

    -- Processes all the variables at a given node
    processNode :: Map.Map Node (Set.Set Var) -> Map.Map (Node, Var) Decision
      -> Node -> PassM (Map.Map (Node, Var) Decision)
    processNode mvs m n 
      = case fmap (readVars . nodeVars . getNodeData) $ lab gr n of
          Nothing -> dieP emptyMeta "Did not find node label during implicit mobility"
          Just rvs -> return $ foldl (process n mvs) m $ Set.toList rvs

    -- Processes a single variable at a given node
    process :: Node -> Map.Map Node (Set.Set Var) -> Map.Map (Node, Var) Decision ->
      Var -> Map.Map (Node, Var) Decision
    process n useAgain prev v =
      Map.insert (n, v)
        (if v `Set.member` Map.findWithDefault Set.empty n useAgain
           then Copy
           else Move) prev

implicitMobility :: A.AST -> PassM A.AST
implicitMobility t
  = do g' <- buildFlowGraph labelFunctions t
              :: PassM (Either String (FlowGraph' PassM UsageLabel (), [Node],
                [Node]))
       case g' of
         Left err -> dieP emptyMeta $ "Error building flow graph: " ++ err
         Right (g, roots, terms) ->
           -- We go from the terminator nodes, because we are performing backward
           -- data-flow analysis
           printMoveCopyDecisions g terms
       return t

