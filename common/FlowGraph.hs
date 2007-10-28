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

module FlowGraph (EdgeLabel(..), FNode(..), FlowGraph, buildFlowGraph, makeFlowGraphInstr) where

import Control.Monad.Error
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive

import qualified AST as A
import Metadata
import Utils

-- | A node will either have zero links out, one or more Seq links, or one or more Par links.
-- Zero links means it is a terminal node.
-- One Seq link means a normal sequential progression.
-- Multiple Seq links means choice.
-- Multiple Par links means a parallel branch.
data EdgeLabel = ESeq | EPar deriving (Show, Eq, Ord)

data OuterType = None | Seq | Par

newtype FNode a = Node (Meta, a)
--type FEdge = (Node, EdgeLabel, Node)

instance Show a => Show (FNode a) where
  show (Node (m,x)) = (filter ((/=) '\"')) $ show m ++ ":" ++ show x

type FlowGraph a = Gr (FNode a) EdgeLabel

type NodesEdges a = ([LNode (FNode a)],[LEdge EdgeLabel])
    
type GraphMaker m a b = ErrorT String (StateT (Node, NodesEdges a) m) b

-- | Builds the instructions to send to GraphViz
makeFlowGraphInstr :: Show a => FlowGraph a -> String
makeFlowGraphInstr = graphviz'

-- The primary reason for having the blank generator take a Meta as an argument is actually for testing.  But other uses can simply ignore it if they want.
buildFlowGraph :: Monad m => (Meta -> m a) -> (forall t. Data t => t -> m a) -> A.Structured -> m (Either String (FlowGraph a))
buildFlowGraph blank f s
  = do res <- runStateT (runErrorT $ buildStructured None s) (0, ([],[]) )
       return $ case res of
                  (Left err,_) -> Left err
                  (_,(_,(nodes, edges))) -> Right (mkGraph nodes edges)
  where
    -- All the functions return the new graph, and the identifier of the node just added
        
    addNode :: Monad m => (Meta, a) -> GraphMaker m a Node
    addNode x = do (n,(nodes, edges)) <- get
                   put (n+1, ((n, Node x):nodes, edges))
                   return n
    
    addEdge :: Monad m => EdgeLabel -> Node -> Node -> GraphMaker m a ()
    addEdge label start end = do (n, (nodes, edges)) <- get
                                 put (n + 1, (nodes,(start, end, label):edges))
    
-- Type commented out because it's not technically correct, but looks right to me:
--    addNode' :: (Monad m, Data t) => Meta -> t -> GraphMaker m a Node
    addNode' m t = do val <- (lift . lift) (f t)
                      addNode (m, val)
    
-- Type commented out because it's not technically correct, but looks right to me:
--    addDummyNode :: Meta -> GraphMaker m a Node
    addDummyNode m = do val <- (lift . lift) (blank m)
                        addNode (m, val)
    
    -- Returns a pair of beginning-node, end-node
-- Type commented out because it's not technically correct, but looks right to me:
--    buildStructured :: OuterType -> A.Structured -> GraphMaker m a (Node, Node)
    buildStructured outer (A.Several m ss) 
      = do nodes <- mapM (buildStructured outer) ss
           case outer of
             None -> -- If there is no context, they should be left as disconnected graphs.
                     do n <- addDummyNode m
                        return (n, n)
             Seq -> do sequence_ $ mapPairs (\(_,s) (e,_) -> addEdge ESeq s e) nodes
                       case nodes of
                         [] -> do n <- addDummyNode m
                                  return (n,n)
                         _ -> return (fst (head nodes), snd (last nodes))
             Par -> do case nodes of
                         [] -> do n <- addDummyNode m
                                  return (n,n)
                         [(s,e)] -> return (s,e)
                         _ -> do
                           nStart <- addDummyNode m
                           nEnd <- addDummyNode m
                           mapM (\(a,z) -> addEdge EPar nStart a >> addEdge ESeq z nEnd) nodes
                           return (nStart, nEnd)
    buildStructured _ (A.OnlyP _ p) = buildProcess p
    buildStructured outer (A.Spec m spec str)
      = do n <- addNode' m spec
           (s,e) <- buildStructured outer str
           addEdge ESeq n s
           return (n,e)
    buildStructured _ s = do n <- addDummyNode (findMeta s)
                             return (n,n)
    
-- Type commented out because it's not technically correct, but looks right to me:
--    buildProcess :: A.Process -> GraphMaker m a (Node, Node)
    buildProcess (A.Seq _ s) = buildStructured Seq s
    buildProcess (A.Par _ _ s) = buildStructured Par s
    buildProcess (A.While m e p)
      = do n <- addNode' m e
           (start, end) <- buildProcess p
           addEdge ESeq n start
           addEdge ESeq end n
           return (n, n)
    buildProcess p = do val <- (lift . lift) (f p)
                        (liftM mkPair) $ addNode (findMeta p, val)
                        
-- TODO keep record of all the types that f is applied to.
-- I think it will end up being Process, Specification, Expression, Variant, Alternative, ExpressionList.
-- So rather than using generics, we could have a small function dictionary instead.

-- Types definitely applied to:
-- A.Specification, A.Process, A.Expression

