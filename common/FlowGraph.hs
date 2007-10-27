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

module FlowGraph (EdgeLabel(..), FlowGraph, buildFlowGraph) where

import Control.Monad.Error
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive

import qualified AST as A
import Metadata
import Utils

data EdgeLabel = EChoice | ESeq | EPar deriving (Show, Eq, Ord)

data OuterType = None | Seq | Par

type FNode a = (Meta, a)
--type FEdge = (Node, EdgeLabel, Node)

type FlowGraph a = Gr (FNode a) EdgeLabel

type NodesEdges a = ([LNode (FNode a)],[LEdge EdgeLabel])
    
type GraphMaker a b = ErrorT String (State (Node, NodesEdges a)) b


buildFlowGraph :: a -> (forall t. Data t => t -> a) -> A.Structured -> Either String (FlowGraph a)
buildFlowGraph blank f s = case runState (runErrorT $ buildStructured None s) (0, ([],[]) ) of
                             (Left err,_) -> Left err
                             (_,(_,(nodes, edges))) -> Right (mkGraph nodes edges)
  where
    -- All the functions return the new graph, and the identifier of the node just added
        
    addNode :: FNode a -> GraphMaker a Node
    addNode x = do (n,(nodes, edges)) <- get
                   put (n+1, ((n, x):nodes, edges))
                   return n
    
    addEdge :: EdgeLabel -> Node -> Node -> GraphMaker a ()
    addEdge label start end = do (n, (nodes, edges)) <- get
                                 put (n + 1, (nodes,(start, end, label):edges))
    
-- Type commented out because it's not technically correct, but looks right to me:
--    addDummyNode :: Meta -> GraphMaker a Node
    addDummyNode m = addNode (m, blank)
    
    -- Returns a pair of beginning-node, end-node
-- Type commented out because it's not technically correct, but looks right to me:
--    buildStructured :: OuterType -> A.Structured -> GraphMaker a (Node, Node)
    buildStructured outer (A.Several m ss) 
      = do nodes <- mapM (buildStructured outer) ss
           case outer of
             None -> throwError "Cannot handle Several without an outer context"
             Seq -> do sequence_ $ mapPairs (\(_,s) (e,_) -> addEdge ESeq s e) nodes
                       case nodes of
                         [] -> do n <- addDummyNode m
                                  return (n,n)
                         _ -> return (fst (head nodes), snd (last nodes))
             Par -> do nStart <- addDummyNode m
                       nEnd <- addDummyNode m
                       mapM (\(a,z) -> addEdge EPar nStart a >> addEdge ESeq z nEnd) nodes
                       return (nStart, nEnd)
    buildStructured _ (A.OnlyP _ p) = buildProcess p
    
-- Type commented out because it's not technically correct, but looks right to me:
--    buildProcess :: A.Process -> GraphMaker a (Node, Node)
    buildProcess (A.Seq _ s) = buildStructured Seq s
    buildProcess (A.Par _ _ s) = buildStructured Par s
    buildProcess p@(A.Skip m) = (liftM mkPair) $ addNode (m, f p)
