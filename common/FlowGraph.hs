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
module FlowGraph (AlterAST(..), EdgeLabel(..), FNode, FlowGraph, FlowGraph', GraphLabelFuncs(..), buildFlowGraph, buildFlowGraphP, getNodeData, getNodeFunc, getNodeMeta, joinLabelFuncs, makeFlowGraphInstr, makeTestNode, mkLabelFuncsConst, mkLabelFuncsGeneric) where

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
data EdgeLabel = ESeq | EStartPar Int | EEndPar Int deriving (Show, Eq, Ord)

--If is (previous condition) (final node)
data OuterType = ONone | OSeq | OPar Int (Node, Node) | OCase (Node,Node) | OIf Node Node deriving (Show)

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
 |AlterArguments (ASTModifier m [A.Formal] structType)
 |AlterExpression (ASTModifier m A.Expression structType)
 |AlterExpressionList (ASTModifier m A.ExpressionList structType)
 |AlterReplicator (ASTModifier m A.Replicator structType)
 |AlterSpec (ASTModifier m A.Specification structType)
 |AlterNothing

data Monad m => FNode' m a b = Node (Meta, a, AlterAST m b)

-- | The label for a node.  A Meta tag, a custom label, and a function
-- for altering the part of the AST that this node came from
type FNode m a = FNode' m a ()
--type FEdge = (Node, EdgeLabel, Node)

instance (Monad m, Show a) => Show (FNode' m a b) where
  show (Node (m,x,_)) = (filter ((/=) '\"')) $ show m ++ ":" ++ show x

type FlowGraph' m a b = Gr (FNode' m a b) EdgeLabel

-- | The main FlowGraph type.  The m parameter is the monad
-- in which alterations to the AST (based on the FlowGraph)
-- must occur.  The a parameter is the type of the node labels.
type FlowGraph m a = FlowGraph' m a ()

-- | A list of nodes and edges.  Used for building up the graph.
type NodesEdges m a b = ([LNode (FNode' m a b)],[LEdge EdgeLabel])

-- | The state carried around when building up the graph.  In order they are:
-- * The next node identifier
-- * The next identifier for a PAR item (for the EStartPar/EEndPar edges)
-- * The list of nodes and edges to put into the graph
-- * The list of root nodes thus far (those with no links to them)
type GraphMakerState mAlter a b = (Node, Int, NodesEdges mAlter a b, [Node])

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
    ,labelExpression :: A.Expression -> m label
    ,labelExpressionList :: A.ExpressionList -> m label
    ,labelReplicator :: A.Replicator -> m label
    ,labelScopeIn :: A.Specification -> m label
    ,labelScopeOut :: A.Specification -> m label
  }

getNodeMeta :: Monad m => FNode' m a b -> Meta
getNodeMeta (Node (m,_,_)) = m

getNodeData :: Monad m => FNode' m a b -> a
getNodeData (Node (_,d,_)) = d

getNodeFunc :: Monad m => FNode' m a b -> AlterAST m b
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
  labelExpression = joinItem labelExpression,
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
mkLabelFuncsConst v = GLF (const v) (const v) (const v) (const v) (const v) (const v) (const v) (const v)

mkLabelFuncsGeneric :: Monad m => (forall t. Data t => t -> m label) -> GraphLabelFuncs m label
mkLabelFuncsGeneric f = GLF f f f f f f f f

  
run :: forall mLabel mAlter label structType b. (Monad mLabel, Monad mAlter) => (GraphLabelFuncs mLabel label -> (b -> mLabel label)) -> b -> GraphMaker mLabel mAlter label structType label
run func x = do f <- asks func
                lift . lift .lift $ f x

addNode :: (Monad mLabel, Monad mAlter) => (Meta, label, AlterAST mAlter structType) -> GraphMaker mLabel mAlter label structType Node
addNode x = do (n,pi,(nodes, edges), rs) <- get
               put (n+1, pi,((n, Node x):nodes, edges), rs)
               return n
    
denoteRootNode :: (Monad mLabel, Monad mAlter) => Node -> GraphMaker mLabel mAlter label structType ()
denoteRootNode root = do (n, pi, nes, roots) <- get
                         put (n, pi, nes, root : roots)
    
addEdge :: (Monad mLabel, Monad mAlter) => EdgeLabel -> Node -> Node -> GraphMaker mLabel mAlter label structType ()
addEdge label start end = do (n, pi, (nodes, edges), rs) <- get
                             -- Edges should only be added after the nodes, so
                             -- for safety here we can check that the nodes exist:
                             if (notElem start $ map fst nodes) || (notElem end $ map fst nodes)
                               then throwError "Could not add edge between non-existent nodes"
                               else put (n + 1, pi, (nodes,(start, end, label):edges), rs)

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
getNextParEdgeId = do (a, pi, b, c) <- get
                      put (a, pi + 1, b, c)
                      return pi

addParEdges :: (Monad mLabel, Monad mAlter) => Int -> (Node,Node) -> [(Node,Node)] -> GraphMaker mLabel mAlter label structType ()
addParEdges usePI (s,e) pairs
  = do (n,pi,(nodes,edges),rs) <- get
       put (n,pi,(nodes,edges ++ (concatMap (parEdge usePI) pairs)),rs)
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

mapMR :: forall inner mAlter mLabel label structType. (Monad mLabel, Monad mAlter) => ASTModifier mAlter [inner] structType -> (inner -> ASTModifier mAlter inner structType -> GraphMaker mLabel mAlter label structType (Node,Node)) -> [inner] -> GraphMaker mLabel mAlter label structType [(Node,Node)]
mapMR outerRoute func xs = mapM funcAndRoute (zip [0..] xs)
  where
    funcAndRoute :: (Int, inner) -> GraphMaker mLabel mAlter label structType (Node,Node)
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
joinPairs m nodes = do sequence_ $ mapPairs (\(_,s) (e,_) -> addEdge ESeq s e) nodes
                       return (fst (head nodes), snd (last nodes))


buildStructuredP :: (Monad mLabel, Monad mAlter) =>
  OuterType -> A.Structured A.Process -> ASTModifier mAlter (A.Structured A.Process) structType -> GraphMaker mLabel mAlter label structType (Either Bool (Node, Node))
buildStructuredP = buildStructured (\_ r p -> buildProcess p r)
buildStructuredC :: (Monad mLabel, Monad mAlter) =>
  OuterType -> A.Structured A.Choice -> ASTModifier mAlter (A.Structured A.Choice) structType -> GraphMaker mLabel mAlter label structType (Either Bool (Node, Node))
buildStructuredC = buildStructured buildOnlyChoice
buildStructuredO :: (Monad mLabel, Monad mAlter) =>
  OuterType -> A.Structured A.Option -> ASTModifier mAlter (A.Structured A.Option) structType -> GraphMaker mLabel mAlter label structType (Either Bool (Node, Node))
buildStructuredO = buildStructured buildOnlyOption

-- Returns a pair of beginning-node, end-node
-- Bool indicates emptiness (False = empty, True = there was something)
buildStructured :: forall a mAlter mLabel label structType. (Monad mLabel, Monad mAlter, Data a) =>
  (OuterType -> ASTModifier mAlter a structType -> a -> GraphMaker mLabel mAlter label structType (Node, Node)) ->
  OuterType -> A.Structured a -> ASTModifier mAlter (A.Structured a) structType -> GraphMaker mLabel mAlter label structType (Either Bool (Node, Node))
buildStructured f outer (A.Several m ss) route
  = do case outer of
         ONone -> -- If there is no context, they should be left as disconnected graphs.
                 do nodes <- mapMRE decompSeveral (buildStructured f outer) ss
                    return $ Left $ nonEmpty nodes
         OSeq -> do nodes <- mapMRE decompSeveral (buildStructured f outer) ss
                    case nodes of
                      Left hadNodes -> return $ Left hadNodes
                      Right nodes' -> joinPairs m nodes' >>* Right
         OPar pId (nStart, nEnd) ->
                do nodes <- mapMRE decompSeveral (buildStructured f outer) ss
                   addParEdges pId (nStart, nEnd) $ either (const []) id nodes
                   return $ Left $ nonEmpty nodes
         --Because the conditions in If statements are chained together, we
         --must fold the specs, not map them independently
         OIf prev end -> foldM foldIf (prev,end) (zip [0..] ss) >>* Right
           where
             foldIf :: (Node,Node) -> (Int,A.Structured a) -> GraphMaker mLabel mAlter label structType (Node, Node)
             foldIf (prev,end) (ind,s) = do nodes <- buildStructured f (OIf prev end) s $ decompSeveral @-> (routeList ind)
                                            case nodes of
                                              Left {} -> return (prev,end)
                                              Right (prev',_) -> return (prev', end)
         _ -> do nodes <- mapMRE decompSeveral (buildStructured f outer) ss
                 return $ Left $ nonEmpty nodes
  where
        decompSeveral :: ASTModifier mAlter [A.Structured a] structType
        decompSeveral = route22 route A.Several

buildStructured f outer (A.Spec m spec str) route
  = do n <- addNode' (findMeta spec) labelScopeIn spec (AlterSpec $ route23 route A.Spec)
       n' <- addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)

       -- If it's a process or function spec we must process it too.  No need to
       -- connect it up to the outer part though
       case spec of
         (A.Specification _ _ (A.Proc m _ args p)) ->
           let procRoute = (route33 (route23 route A.Spec) A.Specification) in
           addNewSubProcFunc m args (Left (p, route44 procRoute A.Proc)) (route34 procRoute A.Proc)
         (A.Specification _ _ (A.Function m _ _ args s)) ->
           let funcRoute = (route33 (route23 route A.Spec) A.Specification) in
           addNewSubProcFunc m args (Right (s, route55 funcRoute A.Function)) (route45 funcRoute A.Function)
         _ -> return ()

       outer' <- case outer of
                   OPar {} -> getNextParEdgeId >>* flip OPar (n,n')
                   _ -> return outer
       nodes <- buildStructured f outer' str (route33 route A.Spec)
       case nodes of
         Left False -> do addEdge ESeq n n'
         Left True -> return ()
         Right (s,e) -> do addEdge ESeq n s
                           addEdge ESeq e n'
       return $ Right (n,n')
buildStructured f outer (A.Rep m rep str) route
  = do let alter = AlterReplicator $ route23 route A.Rep
       case outer of
         OSeq -> do n <- addNode' (findMeta rep) labelReplicator rep alter
                    nodes <- buildStructured f outer str (route33 route A.Rep)
                    case nodes of
                      Right (s,e) ->
                        do addEdge ESeq n s
                           addEdge ESeq e n
                      Left False -> addEdge ESeq n n
                      Left True -> throwError $ show m ++ " SEQ replicator had non-joined up body when building flow-graph"
                    return $ Right (n,n)
         OPar pId _ ->
           do s <- addNode' (findMeta rep) labelReplicator rep alter
              e <- addDummyNode m
              pId <- getNextParEdgeId
              nodes <- buildStructured f (OPar pId (s,e)) str (route33 route A.Rep)
              case nodes of
                Left False -> addEdge ESeq s e
                Left True -> return ()
                Right (s',e') -> do addEdge (EStartPar pId) s s'
                                    addEdge (EEndPar pId) e' e
              return $ Right (s,e)
         OIf prev end ->
           do repNode <- addNode' (findMeta rep) labelReplicator rep alter
              addEdge ESeq prev repNode
              nodes <- buildStructured f (OIf repNode end) str (route33 route A.Rep)
              
              case nodes of
                Left False -> return $ Right (repNode, repNode)
                Left True -> return $ Right (repNode, repNode)
                Right (p,e) -> do addEdge ESeq p repNode
                                  return $ Right (repNode, repNode)
              
              return $ Right (repNode, end)
         _ -> throwError $ "Cannot have replicators inside context: " ++ show outer

buildStructured f outer (A.Only _ o) route = f outer (route22 route A.Only) o >>* Right
buildStructured _ _ s _ = return $ Left False

buildOnlyChoice :: (Monad mLabel, Monad mAlter) => OuterType -> ASTModifier mAlter A.Choice structType -> A.Choice -> GraphMaker mLabel mAlter label structType (Node, Node)
buildOnlyChoice outer route (A.Choice m exp p)
  = do nexp <- addNodeExpression (findMeta exp) exp $ route23 route A.Choice
       (nbodys, nbodye) <- buildProcess p $ route33 route A.Choice
       addEdge ESeq nexp nbodys
       case outer of
         OIf cPrev cEnd ->
           do addEdge ESeq cPrev nexp
              addEdge ESeq nbodye cEnd
         _ -> throwError "Choice found outside IF statement"
       return (nexp,nbodye)

buildOnlyOption :: (Monad mLabel, Monad mAlter) => OuterType -> ASTModifier mAlter A.Option structType -> A.Option -> GraphMaker mLabel mAlter label structType (Node, Node)
buildOnlyOption outer route opt
  = do (s,e) <-
         case opt of
           (A.Option m es p) -> do
             nexpNodes <- mapMR (route23 route A.Option) (\e r -> addNodeExpression (findMeta e) e r >>* mkPair) es
             (nexps, nexpe) <- joinPairs m nexpNodes
             (nbodys, nbodye) <- buildProcess p $ route33 route A.Option
             addEdge ESeq nexpe nbodys
             return (nexps,nbodye)
           (A.Else _ p) -> buildProcess p $ route22 route A.Else
       case outer of
         OCase (cStart, cEnd) ->
           do addEdge ESeq cStart s
              addEdge ESeq e cEnd
         _ -> throwError "Option found outside CASE statement"
       return (s,e)

addNewSubProcFunc :: (Monad mLabel, Monad mAlter) => 
  Meta -> [A.Formal] -> Either (A.Process, ASTModifier mAlter A.Process structType) (A.Structured A.ExpressionList, ASTModifier mAlter (A.Structured A.ExpressionList) structType) ->
      ASTModifier mAlter [A.Formal] structType -> GraphMaker mLabel mAlter label structType ()
addNewSubProcFunc m args body argsRoute
  = do root <- addNode' m labelStartNode (m, args) (AlterArguments argsRoute)
       denoteRootNode root
       bodyNode <- case body of
         Left (p,route) -> buildProcess p route >>* fst
         Right (s,route) ->
           do s <- buildStructured (buildEL m) ONone s route
              case s of
                Left {} -> throwError $ show m ++ " Expected VALOF or specification at top-level of function when building flow-graph"
                Right (n,_) -> return n            
       addEdge ESeq root bodyNode
  where
        buildEL m _ r el = addNodeExpressionList m el r >>* mkPair

buildProcess :: (Monad mLabel, Monad mAlter) => A.Process -> ASTModifier mAlter A.Process structType -> GraphMaker mLabel mAlter label structType (Node, Node)
buildProcess (A.Seq m s) route
  = do s <- buildStructuredP OSeq s (route22 route A.Seq)
       case s of
         Left True -> throwError $ show m ++ " SEQ had non-joined up body when building flow-graph"
         Left False -> do n <- addDummyNode m
                          return (n, n)
         Right ns -> return ns
buildProcess (A.Par m _ s) route
  = do nStart <- addDummyNode m
       nEnd <- addDummyNode m
       pId <- getNextParEdgeId
       nodes <- buildStructuredP (OPar pId (nStart, nEnd)) s (route33 route A.Par)
       case nodes of
         Left False -> do addEdge ESeq nStart nEnd -- no processes in PAR, join start and end with simple ESeq link
         Left True -> return () -- already wired up
         Right (start, end) ->
              do addEdge (EStartPar pId) nStart start
                 addEdge (EEndPar pId) end nEnd
       return (nStart, nEnd)
buildProcess (A.While _ e p) route
  = do n <- addNodeExpression (findMeta e) e (route23 route A.While)
       (start, end) <- buildProcess p (route33 route A.While)
       addEdge ESeq n start
       addEdge ESeq end n
       return (n, n)
buildProcess (A.Case m e s) route
  = do nStart <- addNodeExpression (findMeta e) e (route23 route A.Case)
       nEnd <- addDummyNode m
       buildStructuredO (OCase (nStart,nEnd)) s (route33 route A.Case)
       return (nStart, nEnd)
buildProcess (A.If m s) route
  = do nStart <- addDummyNode m
       nEnd <- addDummyNode m
       buildStructuredC (OIf nStart nEnd) s (route22 route A.If)
       return (nStart, nEnd)
buildProcess p route = addNode' (findMeta p) labelProcess p (AlterProcess route) >>* mkPair



-- | Builds a control-flow-graph.  The mAlter monad is the monad in which
-- AST alterations would take place.  Note that mAlter does not feature in
-- the parameters, only in the result.  The mLabel monad is the monad in
-- which the labelling must be done; hence the flow-graph is returned inside
-- the label monad.
buildFlowGraph :: forall mLabel mAlter label structType. (Monad mLabel, Monad mAlter, Data structType) =>
  GraphLabelFuncs mLabel label ->
  A.Structured structType ->
  mLabel (Either String (FlowGraph' mAlter label structType, [Node]))
buildFlowGraph funcs s
  = do res <- flip runStateT (0, 0, ([],[]), []) $ flip runReaderT funcs $ runErrorT $ buildStructured (\_ _ _ -> throwError "Did not expect outer-most node to exist in AST") ONone s id
       return $ case res of
                  (Left err,_) -> Left err
                  (Right (Left {}),(_,_,(nodes, edges),roots)) -> Right (mkGraph nodes edges, roots)
                  (Right (Right (root,_)),(_,_,(nodes, edges),roots)) -> Right (mkGraph nodes edges, root : roots)

buildFlowGraphP :: forall mLabel mAlter label. (Monad mLabel, Monad mAlter) =>
  GraphLabelFuncs mLabel label ->
  A.Structured A.Process ->
  mLabel (Either String (FlowGraph' mAlter label A.Process, [Node]))
buildFlowGraphP funcs s
  = do res <- flip runStateT (0, 0, ([],[]), []) $ flip runReaderT funcs $ runErrorT $ buildStructuredP ONone s id
       return $ case res of
                  (Left err,_) -> Left err
                  (Right (Left {}),(_,_,(nodes, edges),roots)) -> Right (mkGraph nodes edges, roots)
                  (Right (Right (root,_)),(_,_,(nodes, edges),roots)) -> Right (mkGraph nodes edges, root : roots)

    
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
