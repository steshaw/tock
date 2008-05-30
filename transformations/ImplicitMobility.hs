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

module ImplicitMobility where

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
printMoveCopyDecisions :: Monad m => FlowGraph m UsageLabel -> Node -> PassM ()
printMoveCopyDecisions gr n
  = case calculateUsedAgainAfter gr n of
      Left err -> dieP (getNodeMeta $ fromJust $ lab gr n) err
      Right mvs -> mapMapWithKeyM f mvs >> return ()
  where
    f :: Node -> (Set.Set Var) -> PassM (Set.Set Var)
    f n vs = case liftM (readVars . nodeVars . getNodeData) $ lab gr n of
               Nothing -> dieP emptyMeta "Did not find label in pmcd"
               Just rv -> (mapM_ g $ Set.toList rv) >> return vs
      where
        g :: Var -> PassM ()
        g v | Set.member v vs = liftIO . putStrLn $ show (findMeta v) ++ " COPY"
            | otherwise = liftIO . putStrLn $ show (findMeta v) ++ " MOVE"


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
           (liftIO $ putStrLn $ makeFlowGraphInstr g) >>
           mapM_ (printMoveCopyDecisions g) terms
       return t

