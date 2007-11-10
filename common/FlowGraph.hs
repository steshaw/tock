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


-- | The module for building control-flow graphs.  Most statements are merely processed as-is (one statement becomes one node).
-- The only cases of interest are the control structures.
--
-- * Seq blocks are merely strung together with ESeq edges.
--
-- * Par blocks have a dummy begin and end node.  The begin node has outgoing links
-- to all the members (EStartPar n), and the end nodes of each of the members has
-- a link (EEndPar n) back to the the dummy end node.  Thus all the par members thread
-- back through the same common node at the end.
--
-- * While loops have a condition node representing the test-expression.  This condition node
-- has an ESeq link out to the body of the while loop, and there is an ESeq link back from the
-- end of the while loop to the condition node.  It is the condition node that is linked
-- to nodes before and after it.
--
-- * Case statements have a slight optimisation.  Technically, the cases are examined in some
-- (probably undefined) order, with an Else option coming last.  But since the expressions
-- to check against are constant, I have chosen to represent case statements as follows:
-- There is a dummy begin node with the test-expression.  This has ESeq links to all possible options.
-- The end of each option links back to a dummy end node.
--
-- * If statements, on the other hand, have to be chained together.  Each expression is connected
-- to its body, but also to the next expression.  There is no link between the last expression
-- and the end of the if; if statements behave like STOP if nothing is matched.
module FlowGraph (AlterAST(..), EdgeLabel(..), FNode(..), FlowGraph, GraphLabelFuncs(..), buildFlowGraph, makeFlowGraphInstr) where

import Control.Monad.Error
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive

import qualified AST as A
import Metadata
import TreeUtil
import Utils

-- | A node will either have zero links out, one or more Seq links, or one or more Par links.
-- Zero links means it is a terminal node.
-- One Seq link means a normal sequential progression.
-- Multiple Seq links means choice.
-- Multiple Par links means a parallel branch.  All outgoing par links should have the same identifier,
-- and this identifier is unique and matches a later endpar link
data EdgeLabel = ESeq | EStartPar Int | EEndPar Int deriving (Show, Eq, Ord)

--If is (previous condition) (final node)
data OuterType = None | Seq | Par | Case (Node,Node) | If Node Node

-- | A type used to build up tree-modifying functions.  When given an inner modification function,
-- it returns a modification function for the whole tree.  The functions are monadic, to
-- provide flexibility; you can always use the Identity monad.
type ASTModifier m inner = (inner -> m inner) -> (A.Structured -> m A.Structured)

-- | An operator for combining ASTModifier functions as you walk the tree.
-- While its implementation is simple, it adds clarity to the code.
(@->) :: ASTModifier m outer -> ((inner -> m inner) -> (outer -> m outer)) -> ASTModifier m inner
(@->) = (.)

-- | A choice of AST altering functions built on ASTModifier.
data AlterAST m = 
  AlterProcess (ASTModifier m A.Process)
 |AlterExpression (ASTModifier m A.Expression)
 |AlterExpressionList (ASTModifier m A.ExpressionList)
 |AlterSpec (ASTModifier m A.Specification)
 |AlterNothing

data Monad m => FNode m a = Node (Meta, a, AlterAST m)
--type FEdge = (Node, EdgeLabel, Node)

instance (Monad m, Show a) => Show (FNode m a) where
  show (Node (m,x,_)) = (filter ((/=) '\"')) $ show m ++ ":" ++ show x

type FlowGraph m a = Gr (FNode m a) EdgeLabel

type NodesEdges m a = ([LNode (FNode m a)],[LEdge EdgeLabel])

type GraphMaker m a b = ErrorT String (StateT (Node, Int, NodesEdges m a) m) b

data Monad m => GraphLabelFuncs m label = GLF {
     labelDummy :: Meta -> m label
    ,labelProcess :: A.Process -> m label
    ,labelExpression :: A.Expression -> m label
    ,labelExpressionList :: A.ExpressionList -> m label
    ,labelScopeIn :: A.Specification -> m label
    ,labelScopeOut :: A.Specification -> m label
  }

-- | Builds the instructions to send to GraphViz
makeFlowGraphInstr :: (Monad m, Show a) => FlowGraph m a -> String
makeFlowGraphInstr = graphviz'

-- The primary reason for having the blank generator take a Meta as an argument is actually for testing.  But other uses can simply ignore it if they want.
buildFlowGraph :: forall m label. Monad m => GraphLabelFuncs m label -> A.Structured -> m (Either String (FlowGraph m label))
buildFlowGraph funcs s
  = do res <- runStateT (runErrorT $ buildStructured None s id) (0, 0, ([],[]) )
       return $ case res of
                  (Left err,_) -> Left err
                  (_,(_,_,(nodes, edges))) -> Right (mkGraph nodes edges)
  where
    -- All the functions return the new graph, and the identifier of the node just added
    
    run :: (GraphLabelFuncs m label -> (b -> m label)) -> b -> m label
    run func = func funcs
        
    addNode :: (Meta, label, AlterAST m) -> GraphMaker m label Node
    addNode x = do (n,pi,(nodes, edges)) <- get
                   put (n+1, pi,((n, Node x):nodes, edges))
                   return n
    
    addEdge :: EdgeLabel -> Node -> Node -> GraphMaker m label ()
    addEdge label start end = do (n, pi, (nodes, edges)) <- get
                                 put (n + 1, pi, (nodes,(start, end, label):edges))
    
    addNode' :: Meta -> (GraphLabelFuncs m label -> (b -> m label)) -> b -> AlterAST m -> GraphMaker m label Node
    addNode' m f t r = do val <- (lift . lift) (run f t)
                          addNode (m, val, r)
    
    addNodeExpression :: Meta -> A.Expression -> (ASTModifier m A.Expression) -> GraphMaker m label Node
    addNodeExpression m e r = addNode' m labelExpression e (AlterExpression r)

    addNodeExpressionList :: Meta -> A.ExpressionList -> (ASTModifier m A.ExpressionList) -> GraphMaker m label Node
    addNodeExpressionList m e r = addNode' m labelExpressionList e (AlterExpressionList r)
    
    addDummyNode :: Meta -> GraphMaker m label Node
    addDummyNode m = addNode' m labelDummy m AlterNothing
    
    addParEdges :: Node -> Node -> [(Node,Node)] -> GraphMaker m label ()
    addParEdges s e pairs = do (n,pi,(nodes,edges)) <- get
                               put (n,pi+1,(nodes,edges ++ (concatMap (parEdge pi) pairs)))
      where
        parEdge :: Int -> (Node, Node) -> [LEdge EdgeLabel]
        parEdge id (a,z) = [(s,a,(EStartPar id)),(z,e,(EEndPar id))]
    
    -- The build-up functions are all of type (innerType -> m innerType) -> outerType -> m outerType
    -- which has the synonym Route m innerType outerType

    getN :: Int -> [a] -> ([a],a,[a])
    getN n xs = let (f,(m:e)) = splitAt n xs in (f,m,e)

    routeList :: Int -> (a -> m a) -> ([a] -> m [a])
    routeList n f xs
      = do let (pre,x,suf) = getN n xs
           x' <- f x
           return (pre ++ [x'] ++ suf)
    
    mapMR :: forall inner. ASTModifier m [inner] -> (inner -> ASTModifier m inner -> GraphMaker m label (Node,Node)) -> [inner] -> GraphMaker m label [(Node,Node)]
    mapMR outerRoute func xs = mapM funcAndRoute (zip [0..] xs)
      where
        funcAndRoute :: (Int, inner) -> GraphMaker m label (Node,Node)
        funcAndRoute (ind,x) = func x (outerRoute @-> routeList ind)
        
    joinPairs :: Meta -> [(Node, Node)] -> GraphMaker m label (Node, Node)
    joinPairs m [] = addDummyNode m >>* mkPair
    joinPairs m nodes = do sequence_ $ mapPairs (\(_,s) (e,_) -> addEdge ESeq s e) nodes
                           return (fst (head nodes), snd (last nodes))
    
    
    -- Returns a pair of beginning-node, end-node
    buildStructured :: OuterType -> A.Structured -> ASTModifier m A.Structured -> GraphMaker m label (Node, Node)
    buildStructured outer (A.Several m ss) route
      = do case outer of
             None -> -- If there is no context, they should be left as disconnected graphs.
                     do nodes <- mapMR decompSeveral (buildStructured outer) ss
                        n <- addDummyNode m
                        return (n, n)
             Seq -> do nodes <- mapMR decompSeveral (buildStructured outer) ss
                       joinPairs m nodes
             Par -> do nodes <- mapMR decompSeveral (buildStructured outer) ss
                       case nodes of
                         [] -> do n <- addDummyNode m
                                  return (n,n)
                         [(s,e)] -> return (s,e)
                         _ -> do
                           nStart <- addDummyNode m
                           nEnd <- addDummyNode m
                           addParEdges nStart nEnd nodes
                           return (nStart, nEnd)
             --Because the conditions in If statements are chained together, we
             --must fold the specs, not map them independently
             If prev end -> foldM foldIf (prev,end) (zip [0..] ss)
               where
                 -- Type commented out because it's not technically correct, but looks right to me:
                 foldIf :: (Node,Node) -> (Int,A.Structured) -> GraphMaker m label (Node, Node)
                 foldIf (prev,end) (ind,s) = do (prev',_) <- buildStructured (If prev end) s $ decompSeveral @-> (routeList ind)
                                                return (prev', end)
             _ -> do nodes <- mapMR decompSeveral (buildStructured outer) ss
                     return (-1,-1)
      where
        decompSeveral :: ASTModifier m [A.Structured]
        decompSeveral = route22 route A.Several
        
    buildStructured _ (A.OnlyP _ p) route = buildProcess p (route22 route A.OnlyP)
    buildStructured outer (A.OnlyC _ (A.Choice m exp p)) route
      = do nexp <- addNodeExpression (findMeta exp) exp $ route @-> (\f (A.OnlyC m (A.Choice m' exp p)) -> do {exp' <- f exp; return (A.OnlyC m (A.Choice m' exp' p))})
           (nbodys, nbodye) <- buildProcess p $ route @-> (\f (A.OnlyC m (A.Choice m' exp p)) -> f p >>* ((A.OnlyC m) . (A.Choice m' exp)))
           addEdge ESeq nexp nbodys
           case outer of
             If cPrev cEnd ->
               do addEdge ESeq cPrev nexp
                  addEdge ESeq nbodye cEnd
             _ -> throwError "Choice found outside IF statement"
           return (nexp,nbodye)
    buildStructured outer (A.OnlyO _ opt) route
      = do (s,e) <-
             case opt of
               (A.Option m es p) -> do
                 nexpNodes <- mapMR (route @-> (\f (A.OnlyO m (A.Option m2 es p)) -> do {es' <- f es; return $ A.OnlyO m $ A.Option m2 es' p})) (\e r -> addNodeExpression (findMeta e) e r >>* mkPair) es
                 (nexps, nexpe) <- joinPairs m nexpNodes
                 (nbodys, nbodye) <- buildProcess p $ route @-> (\f (A.OnlyO m (A.Option m2 es p)) -> f p >>* ((A.OnlyO m) . (A.Option m2 es)))
                 addEdge ESeq nexpe nbodys
                 return (nexps,nbodye)
               (A.Else _ p) -> buildProcess p $ route @-> (\f (A.OnlyO m (A.Else m2 p)) -> f p >>* ((A.OnlyO m) . (A.Else m2)))
           case outer of
             Case (cStart, cEnd) ->
               do addEdge ESeq cStart s
                  addEdge ESeq e cEnd
             _ -> throwError "Option found outside CASE statement"
           return (s,e)
    buildStructured outer (A.Spec m spec str) route
      = do n <- addNode' m labelScopeIn spec (AlterSpec $ route23 route A.Spec)
           n' <- addNode' m labelScopeOut spec (AlterSpec $ route23 route A.Spec)
           (s,e) <- buildStructured outer str (route33 route A.Spec)
           addEdge ESeq n s
           addEdge ESeq e n'
           return (n,n')
    buildStructured _ s _ = do n <- addDummyNode (findMeta s)
                               return (n,n)
    
    buildProcess :: A.Process -> ASTModifier m A.Process -> GraphMaker m label (Node, Node)
    buildProcess (A.Seq _ s) route = buildStructured Seq s (route22 route A.Seq)
    buildProcess (A.Par _ _ s) route = buildStructured Par s (route33 route A.Par)
    buildProcess (A.While m e p) route
      = do n <- addNodeExpression m e (route23 route A.While)
           (start, end) <- buildProcess p (route33 route A.While)
           addEdge ESeq n start
           addEdge ESeq end n
           return (n, n)
    buildProcess (A.Case m e s) route
      = do nStart <- addNodeExpression (findMeta e) e (route23 route A.Case)
           nEnd <- addDummyNode m
           buildStructured (Case (nStart,nEnd)) s (route33 route A.Case)
           return (nStart, nEnd)
    buildProcess (A.If m s) route
      = do nStart <- addDummyNode m
           nEnd <- addDummyNode m
           buildStructured (If nStart nEnd) s (route22 route A.If)
           return (nStart, nEnd)
    buildProcess p route = addNode' (findMeta p) labelProcess p (AlterProcess route) >>* mkPair

decomp22 :: (Monad m, Data a, Typeable a0, Typeable a1) => (a0 -> a1 -> a) -> (a1 -> m a1) -> (a -> m a)
decomp22 con f1 = decomp2 con return f1

decomp23 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => (a0 -> a1 -> a2 -> a) -> (a1 -> m a1) -> (a -> m a)
decomp23 con f1 = decomp3 con return f1 return

decomp33 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => (a0 -> a1 -> a2 -> a) -> (a2 -> m a2) -> (a -> m a)
decomp33 con f2 = decomp3 con return return f2

route22 :: (Monad m, Data a, Typeable a0, Typeable a1) => ASTModifier m a -> (a0 -> a1 -> a) -> ASTModifier m a1
route22 route con = route @-> (decomp22 con)

route23 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => ASTModifier m a -> (a0 -> a1 -> a2 -> a) -> ASTModifier m a1
route23 route con = route @-> (decomp23 con)

route33 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => ASTModifier m a -> (a0 -> a1 -> a2 -> a) -> ASTModifier m a2
route33 route con = route @-> (decomp33 con)
