{-
Tock: a compiler for parallel languages
Copyright (C) 2007-2008 University of Kent

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

module FlowUtils where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive hiding (run)

import qualified AST as A
import Metadata
import TreeUtils
import Utils

-- | A node will either have:
-- * zero links out,
-- * one or more Seq links out,
-- * ot one or more Par links out.
-- Zero links means it is a terminal node.
-- One Seq link means a normal sequential progression.
-- Multiple Seq links means choice.
-- Multiple Par links means a parallel branch.  All outgoing par links should have the same identifier,
-- and this identifier is unique and matches a later endpar link
data EdgeLabel = ESeq (Maybe Bool) | EStartPar Int | EEndPar Int deriving (Show, Eq, Ord)

-- | A type used to build up tree-modifying functions.  When given an inner modification function,
-- it returns a modification function for the whole tree.  The functions are monadic, to
-- provide flexibility; you can always use the Identity monad.
type ASTModifier m inner structType = (inner -> m inner) -> (A.Structured structType -> m (A.Structured structType))

-- | An operator for combining ASTModifier functions as you walk the tree.
-- While its implementation is simple, it adds clarity to the code.
(@->) :: ASTModifier m outer b -> ((inner -> m inner) -> (outer -> m outer)) -> ASTModifier m inner b
(@->) = (.)

-- | A choice of AST altering functions built on ASTModifier.
data AlterAST m structType = 
  AlterProcess (ASTModifier m A.Process structType)
 |AlterAlternative (ASTModifier m A.Alternative structType)
 |AlterArguments (ASTModifier m [A.Formal] structType)
 |AlterExpression (ASTModifier m A.Expression structType)
 |AlterExpressionList (ASTModifier m A.ExpressionList structType)
 |AlterReplicator (ASTModifier m A.Replicator structType)
 |AlterSpec (ASTModifier m A.Specification structType)
 |AlterNothing

data Monad mAlter => FNode' structType mAlter label
  = Node (Meta, label, AlterAST mAlter structType)

instance Monad m => Functor (FNode' s m) where
  fmap f (Node (m, l, a)) = Node (m, f l, a)

-- | The label for a node.  A Meta tag, a custom label, and a function
-- for altering the part of the AST that this node came from
type FNode mAlter label = FNode' () mAlter label
--type FEdge = (Node, EdgeLabel, Node)

instance (Monad m, Show a) => Show (FNode' b m a) where
  show (Node (m,x,_)) = (filter ((/=) '\"')) $ show m ++ ":" ++ show x

type FlowGraph' mAlter label structType = Gr (FNode' structType mAlter label) EdgeLabel

-- | The main FlowGraph type.  The mAlter parameter is the monad
-- in which alterations to the AST (based on the FlowGraph)
-- must occur.  The label parameter is the type of the node labels.
type FlowGraph mAlter label = FlowGraph' mAlter label ()

-- | A list of nodes and edges.  Used for building up the graph.
type NodesEdges m a b = ([LNode (FNode' b m a)],[LEdge EdgeLabel])

-- | The state carried around when building up the graph.  In order they are:
-- * The next node identifier
-- * The next identifier for a PAR item (for the EStartPar\/EEndPar edges)
-- * The list of nodes and edges to put into the graph
-- * The list of root nodes thus far (those with no links to them)
-- * The list of terminator nodes thus far (those with no links from them)
type GraphMakerState mAlter a b = (Node, Int, NodesEdges mAlter a b, [Node], [Node])

type GraphMaker mLabel mAlter a b c = ErrorT String (ReaderT (GraphLabelFuncs mLabel a) (StateT (GraphMakerState mAlter a b) mLabel)) c

-- | The GraphLabelFuncs type.  These are a group of functions
-- used to provide labels for different elements of AST.
-- The m parameter is the monad the labelling must take place in,
-- and the label parameter is of course the label type.
-- The primary reason for having the blank (dummy) generator take a
-- Meta as an argument is actually for testing.  But other uses 
-- can simply ignore it if they want.
data Monad m => GraphLabelFuncs m label = GLF {
     labelDummy :: Meta -> m label
    ,labelStartNode :: (Meta, [A.Formal]) -> m label
    ,labelProcess :: A.Process -> m label
    ,labelAlternative :: A.Alternative -> m label
    ,labelExpression :: A.Expression -> m label
    , labelConditionalExpression :: A.Expression -> m label
    ,labelExpressionList :: A.ExpressionList -> m label
    ,labelReplicator :: (A.Name, A.Replicator) -> m label
    ,labelScopeIn :: A.Specification -> m label
    ,labelScopeOut :: A.Specification -> m label
  }

getNodeMeta :: Monad m => FNode' b m a -> Meta
getNodeMeta (Node (m,_,_)) = m

getNodeData :: Monad m => FNode' b m a -> a
getNodeData (Node (_,d,_)) = d

getNodeFunc :: Monad m => FNode' b m a -> AlterAST m b
getNodeFunc (Node (_,_,f)) = f

makeTestNode :: Monad m => Meta -> a -> FNode m a
makeTestNode m d = Node (m,d,undefined)

-- | Builds the instructions to send to GraphViz
makeFlowGraphInstr :: (Monad m, Show a, Data b) => FlowGraph' m a b -> String
makeFlowGraphInstr = graphviz'

-- | Joins two labelling functions together.  They must use the same monad.
joinLabelFuncs :: forall a b m. Monad m => GraphLabelFuncs m a -> GraphLabelFuncs m b -> GraphLabelFuncs m (a,b)
joinLabelFuncs fx fy = GLF
 {
  labelDummy = joinItem labelDummy,
  labelStartNode = joinItem labelStartNode,
  labelProcess = joinItem labelProcess,
  labelAlternative = joinItem labelAlternative,
  labelExpression = joinItem labelExpression,
  labelConditionalExpression = joinItem labelConditionalExpression,
  labelExpressionList = joinItem labelExpressionList,
  labelReplicator = joinItem labelReplicator,
  labelScopeIn = joinItem labelScopeIn,
  labelScopeOut = joinItem labelScopeOut
 }
  where
    joinItem :: (forall l. GraphLabelFuncs m l -> (k -> m l)) -> (k -> m (a,b))
    joinItem item = joinTwo (item fx) (item fy)
  
    joinTwo :: (a' -> m b') -> (a' -> m c') -> (a' -> m (b',c'))
    joinTwo f0 f1 x = do x0 <- f0 x
                         x1 <- f1 x
                         return (x0,x1)

mkLabelFuncsConst :: Monad m => m label -> GraphLabelFuncs m label
mkLabelFuncsConst v = GLF (const v) (const v) (const v) (const v) (const v) (const v) (const v) (const v) (const v) (const v)

mkLabelFuncsGeneric :: Monad m => (forall t. Data t => t -> m label) -> GraphLabelFuncs m label
mkLabelFuncsGeneric f = GLF f f f f f f f f f f

  
run :: forall mLabel mAlter label structType b. (Monad mLabel, Monad mAlter) => (GraphLabelFuncs mLabel label -> (b -> mLabel label)) -> b -> GraphMaker mLabel mAlter label structType label
run func x = do f <- asks func
                lift . lift .lift $ f x

addNode :: (Monad mLabel, Monad mAlter) => (Meta, label, AlterAST mAlter structType) -> GraphMaker mLabel mAlter label structType Node
addNode x = do (n,pi,(nodes, edges), rs, ts) <- get
               put (n+1, pi,((n, Node x):nodes, edges), rs, ts)
               return n
    
denoteRootNode :: (Monad mLabel, Monad mAlter) => Node -> GraphMaker mLabel mAlter label structType ()
denoteRootNode root = do (n, pi, nes, roots, ts) <- get
                         put (n, pi, nes, root : roots, ts)

denoteTerminatorNode :: (Monad mLabel, Monad mAlter) => Node -> GraphMaker mLabel mAlter label structType ()
denoteTerminatorNode t = do (n, pi, nes, roots, ts) <- get
                            put (n, pi, nes, roots, t : ts)

    
addEdge :: (Monad mLabel, Monad mAlter) => EdgeLabel -> Node -> Node -> GraphMaker mLabel mAlter label structType ()
addEdge label start end = do (n, pi, (nodes, edges), rs, ts) <- get
                             -- Edges should only be added after the nodes, so
                             -- for safety here we can check that the nodes exist:
                             if (notElem start $ map fst nodes) || (notElem end $ map fst nodes)
                               then throwError "Could not add edge between non-existent nodes"
                               else put (n + 1, pi, (nodes,(start, end, label):edges), rs,
                                 ts)

-- It is important for the flow-graph tests that the Meta tag passed in is the same as the
-- result of calling findMeta on the third parameter
addNode' :: (Monad mLabel, Monad mAlter) => Meta -> (GraphLabelFuncs mLabel label -> (b -> mLabel label)) -> b -> AlterAST mAlter structType -> GraphMaker mLabel mAlter label structType Node
addNode' m f t r = do val <- run f t
                      addNode (m, val, r)
    
addNodeExpression :: (Monad mLabel, Monad mAlter) => Meta -> A.Expression -> (ASTModifier mAlter A.Expression structType) -> GraphMaker mLabel mAlter label structType Node
addNodeExpression m e r = addNode' m labelExpression e (AlterExpression r)

addNodeExpressionList :: (Monad mLabel, Monad mAlter) => Meta -> A.ExpressionList -> (ASTModifier mAlter A.ExpressionList structType) -> GraphMaker mLabel mAlter label structType Node
addNodeExpressionList m e r = addNode' m labelExpressionList e (AlterExpressionList r)

addDummyNode :: (Monad mLabel, Monad mAlter) => Meta -> GraphMaker mLabel mAlter label structType Node
addDummyNode m = addNode' m labelDummy m AlterNothing

getNextParEdgeId :: (Monad mLabel, Monad mAlter) => GraphMaker mLabel mAlter label structType Int
getNextParEdgeId = do (a, pi, b, c, d) <- get
                      put (a, pi + 1, b, c, d)
                      return pi

addParEdges :: (Monad mLabel, Monad mAlter) => Int -> (Node,Node) -> [(Node,Node)] -> GraphMaker mLabel mAlter label structType ()
addParEdges usePI (s,e) pairs
  = do (n,pi,(nodes,edges),rs,ts) <- get
       put (n,pi,(nodes,edges ++ (concatMap (parEdge usePI) pairs)),rs,ts)
  where
    parEdge :: Int -> (Node, Node) -> [LEdge EdgeLabel]
    parEdge id (a,z) = [(s,a,(EStartPar id)),(z,e,(EEndPar id))]

-- The build-up functions are all of type (innerType -> m innerType) -> outerType -> m outerType
-- which has the synonym Route m innerType outerType

getN :: Int -> [a] -> ([a],a,[a])
getN n xs = let (f,(m:e)) = splitAt n xs in (f,m,e)

routeList :: Monad m => Int -> (a -> m a) -> ([a] -> m [a])
routeList n f xs
  = do let (pre,x,suf) = getN n xs
       x' <- f x
       return (pre ++ [x'] ++ suf)

mapMR :: forall inner mAlter mLabel label retType structType. (Monad mLabel, Monad mAlter) =>
  ASTModifier mAlter [inner] structType ->
  (inner -> ASTModifier mAlter inner structType -> GraphMaker mLabel mAlter label structType retType) ->
  [inner] -> GraphMaker mLabel mAlter label structType [retType]
mapMR outerRoute func xs = mapM funcAndRoute (zip [0..] xs)
  where
    funcAndRoute :: (Int, inner) -> GraphMaker mLabel mAlter label structType retType
    funcAndRoute (ind,x) = func x (outerRoute @-> routeList ind)


mapMRE :: forall inner mAlter mLabel label structType. (Monad mLabel, Monad mAlter) => ASTModifier mAlter [inner] structType -> (inner -> ASTModifier mAlter inner structType -> GraphMaker mLabel mAlter label structType (Either Bool (Node,Node))) -> [inner] -> GraphMaker mLabel mAlter label structType (Either Bool [(Node,Node)])
mapMRE outerRoute func xs = mapM funcAndRoute (zip [0..] xs) >>* foldl foldEither (Left False)
  where
    foldEither :: Either Bool [(Node,Node)] -> Either Bool (Node,Node) -> Either Bool [(Node,Node)]
    foldEither (Left _) (Right n) = Right [n]
    foldEither (Right ns) (Left _) = Right ns
    foldEither (Left hadNode) (Left hadNode') = Left $ hadNode || hadNode'
    foldEither (Right ns) (Right n) = Right (ns ++ [n])

    funcAndRoute :: (Int, inner) -> GraphMaker mLabel mAlter label structType (Either Bool (Node,Node))
    funcAndRoute (ind,x) = func x (outerRoute @-> routeList ind)
  

nonEmpty :: Either Bool [(Node,Node)] -> Bool
nonEmpty (Left hadNodes) = hadNodes
nonEmpty (Right nodes) = not (null nodes)
    
joinPairs :: (Monad mLabel, Monad mAlter) => Meta -> [(Node, Node)] -> GraphMaker mLabel mAlter label structType (Node, Node)
joinPairs m [] = addDummyNode m >>* mkPair
joinPairs m nodes = do sequence_ $ mapPairs (\(_,s) (e,_) -> addEdge (ESeq
                         Nothing) s e) nodes
                       return (fst (head nodes), snd (last nodes))

decomp22 :: (Monad m, Data a, Typeable a0, Typeable a1) => (a0 -> a1 -> a) -> (a1 -> m a1) -> (a -> m a)
decomp22 con f1 = decomp2 con return f1

decomp23 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => (a0 -> a1 -> a2 -> a) -> (a1 -> m a1) -> (a -> m a)
decomp23 con f1 = decomp3 con return f1 return

decomp33 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => (a0 -> a1 -> a2 -> a) -> (a2 -> m a2) -> (a -> m a)
decomp33 con f2 = decomp3 con return return f2

decomp34 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3) =>
  (a0 -> a1 -> a2 -> a3 -> a) -> (a2 -> m a2) -> (a -> m a)
decomp34 con f2 = decomp4 con return return f2 return

decomp44 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3) =>
  (a0 -> a1 -> a2 -> a3 -> a) -> (a3 -> m a3) -> (a -> m a)
decomp44 con f3 = decomp4 con return return return f3

decomp45 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3, Typeable a4) =>
  (a0 -> a1 -> a2 -> a3 -> a4 -> a) -> (a3 -> m a3) -> (a -> m a)
decomp45 con f3 = decomp5 con return return return f3 return

decomp55 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3, Typeable a4) =>
  (a0 -> a1 -> a2 -> a3 -> a4 -> a) -> (a4 -> m a4) -> (a -> m a)
decomp55 con f4 = decomp5 con return return return return f4

route22 :: (Monad m, Data a, Typeable a0, Typeable a1) => ASTModifier m a b -> (a0 -> a1 -> a) -> ASTModifier m a1 b
route22 route con = route @-> (decomp22 con)

route23 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => ASTModifier m a b -> (a0 -> a1 -> a2 -> a) -> ASTModifier m a1 b
route23 route con = route @-> (decomp23 con)

route33 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2) => ASTModifier m a b -> (a0 -> a1 -> a2 -> a) -> ASTModifier m a2 b
route33 route con = route @-> (decomp33 con)

route34 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3) =>
  ASTModifier m a b -> (a0 -> a1 -> a2 -> a3 -> a) -> ASTModifier m a2 b
route34 route con = route @-> (decomp34 con)

route44 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3) =>
  ASTModifier m a b -> (a0 -> a1 -> a2 -> a3 -> a) -> ASTModifier m a3 b
route44 route con = route @-> (decomp44 con)

route45 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3, Typeable a4) =>
  ASTModifier m a b -> (a0 -> a1 -> a2 -> a3 -> a4 -> a) -> ASTModifier m a3 b
route45 route con = route @-> (decomp45 con)

route55 :: (Monad m, Data a, Typeable a0, Typeable a1, Typeable a2, Typeable a3, Typeable a4) =>
  ASTModifier m a b -> (a0 -> a1 -> a2 -> a3 -> a4 -> a) -> ASTModifier m a4 b
route55 route con = route @-> (decomp55 con)
