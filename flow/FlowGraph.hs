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
import Data.Maybe

import qualified AST as A
import Metadata
import FlowUtils
import Utils


addSpecNodes :: (Monad mAlter, Monad mLabel, Data a) => A.Specification -> ASTModifier mAlter (A.Structured a) structType -> GraphMaker mLabel mAlter label structType (Node, Node)
addSpecNodes spec route
  = do n <- addNode' (findMeta spec) labelScopeIn spec (AlterSpec $ route23 route A.Spec)
       n' <- addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)
       return (n, n')

-- Descends into process or function specifications, but doesn't join them up.  Any other specifications are ignored
buildProcessOrFunctionSpec :: (Monad mAlter, Monad mLabel) => A.Specification -> ASTModifier mAlter (A.Specification) structType ->
  GraphMaker mLabel mAlter label structType ()
buildProcessOrFunctionSpec (A.Specification _ _ (A.Proc m _ args p)) route
 = let procRoute = (route33 route A.Specification) in
   addNewSubProcFunc m args (Left (p, route44 procRoute A.Proc)) (route34 procRoute A.Proc)
buildProcessOrFunctionSpec (A.Specification _ _ (A.Function m _ _ args es)) route
  = let funcRoute = (route33 route A.Specification) in
    case es of
      Left sel -> addNewSubProcFunc m args (Right (sel, route55 funcRoute A.Function @-> (\f (Left e) -> f e >>* Left))) (route45 funcRoute A.Function)
      Right p -> addNewSubProcFunc m args (Left (p, route55 funcRoute A.Function @-> (\f (Right p) -> f p >>* Right))) (route45 funcRoute A.Function)
buildProcessOrFunctionSpec _ _ = return ()

-- All the various types of Structured (SEQ, PAR, ALT, IF, CASE, input-CASE, VALOF) deal with their nodes so differently
-- that I have ended up having a different function for each of them, because there is so little commonality
--
-- They differ in many ways, one of the main ones being who has responsibility for adding the links.  In the (easy) case
-- of SEQ, we always return (begin, end) nodes and let the caller draw in the links.  In the case of PAR, the tricky
-- aspect of nested Specs and such means it's better to pass the outermost begin/end nodes for the PAR into the function
-- and let each sub-function draw the links.

buildStructuredAST :: (Monad mLabel, Monad mAlter) => A.Structured () -> ASTModifier mAlter (A.Structured ()) () ->
  GraphMaker mLabel mAlter label () ()
buildStructuredAST (A.Several _ ss) route
  = do mapMR (route22 route A.Several) buildStructuredAST ss
       return () 
buildStructuredAST (A.Spec _ spec str) route
  = do buildProcessOrFunctionSpec spec (route23 route A.Spec)
       buildStructuredAST str (route33 route A.Spec)
buildStructuredAST s _ = throwError $ "Unexpected element at top-level: " ++ show s

buildStructuredEL :: (Monad mLabel, Monad mAlter) => A.Structured A.ExpressionList -> ASTModifier mAlter (A.Structured A.ExpressionList) structType ->
  GraphMaker mLabel mAlter label structType (Node, Node)
buildStructuredEL (A.Only m el) route = addNodeExpressionList m el (route22 route A.Only) >>* mkPair
buildStructuredEL (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       (ss, se) <- buildStructuredEL str (route33 route A.ProcThen)
       addEdge ESeq pe ss
       return (ps, se)
buildStructuredEL (A.Spec m spec str) route
  = do (n,n') <- addSpecNodes spec route
       buildProcessOrFunctionSpec spec (route23 route A.Spec)
       (s,e) <- buildStructuredEL str (route33 route A.Spec)
       addEdge ESeq n s
       addEdge ESeq e n'
       return (n, n')
buildStructuredEL s _ = throwError $ "Unexpected element in function: " ++ show s

buildStructuredAltNoSpecs :: (Monad mLabel, Monad mAlter) => (Node,Node) -> A.Structured A.Alternative -> ASTModifier mAlter (A.Structured A.Alternative) structType ->
  GraphMaker mLabel mAlter label structType ()
  -- On the matter of replicators:
  -- A replicated ALT has several guards, which will be replicated for
  -- different values of i (or whatever).  But leaving aside the issue
  -- of constraints on i (TODO record the replicators in ALTs somehow)
  -- only one of the replicated guards will be chosen, so we can effectively
  -- ignore the replication (in terms of the flow graph at least)
buildStructuredAltNoSpecs se (A.Spec _ _ str) route = buildStructuredAltNoSpecs se str (route33 route A.Spec)
buildStructuredAltNoSpecs se (A.Several m ss) route
  = mapMR (route22 route A.Several) (buildStructuredAltNoSpecs se) ss >> return ()
buildStructuredAltNoSpecs se (A.ProcThen _ _ str) route
  -- ProcThen is considered part of the specs, so we ignore it here
  = buildStructuredAltNoSpecs se str (route33 route A.ProcThen)
buildStructuredAltNoSpecs (nStart, nEnd) (A.Only _ guard) route
  = do (s,e) <- buildOnlyAlternative (route22 route A.Only) guard
       addEdge ESeq nStart s
       addEdge ESeq e nEnd

foldSpecs :: forall mAlter mLabel label structType. (Monad mLabel, Monad mAlter) => [Maybe ((Node, Node), (Node, Node))] -> GraphMaker mLabel mAlter label structType (Maybe ((Node, Node), (Node, Node)))
foldSpecs sps = case catMaybes sps of
    [] -> return Nothing
    (x:xs) -> foldM fold x xs >>* Just
  where
    fold :: ((Node, Node), (Node, Node)) -> ((Node, Node), (Node, Node)) -> GraphMaker mLabel mAlter label structType ((Node, Node), (Node, Node))
    fold ((inStartA, inEndA), (outStartA, outEndA)) ((inStartB, inEndB), (outStartB, outEndB))
      = do addEdge ESeq inEndA inStartB
           addEdge ESeq outEndB outEndA
           return ((inStartA, inEndB), (outStartB, outEndA))

buildJustSpecs :: (Monad mLabel, Monad mAlter, Data a) => A.Structured a -> ASTModifier mAlter (A.Structured a) structType ->
  GraphMaker mLabel mAlter label structType (Maybe ((Node, Node), (Node, Node)))
buildJustSpecs (A.Only {}) _ = return Nothing
buildJustSpecs (A.Several _ ss) route = mapMR (route22 route A.Several) buildJustSpecs ss >>= foldSpecs
buildJustSpecs (A.Spec _ spec str) route
  = do (scopeIn, scopeOut) <- addSpecNodes spec route
       inner <- buildJustSpecs str (route33 route A.Spec)
       case inner of
         Nothing -> return $ Just ((scopeIn, scopeIn), (scopeOut, scopeOut))
         Just ((innerInStart, innerInEnd), (innerOutStart, innerOutEnd)) ->
           do addEdge ESeq scopeIn innerInStart
              addEdge ESeq innerOutEnd scopeOut
              return $ Just ((scopeIn, innerInEnd), (innerOutStart, scopeOut))
buildJustSpecs (A.ProcThen m p str) route
  = do inner <- buildJustSpecs str (route33 route A.ProcThen)
       (procNodeStart, procNodeEnd) <- buildProcess p (route23 route A.ProcThen)
       case inner of
         Nothing -> throwError "ProcThen was used without an inner specification"
         Just ((innerInStart, innerInEnd), innerOut) ->
           do addEdge ESeq procNodeEnd innerInStart
              return $ Just ((procNodeStart, innerInEnd), innerOut)

buildStructuredSeq :: (Monad mLabel, Monad mAlter) => A.Structured A.Process -> ASTModifier mAlter (A.Structured A.Process) structType ->
  GraphMaker mLabel mAlter label structType (Node, Node)
buildStructuredSeq (A.Several m ss) route
  = do nodes <- mapMR (route22 route A.Several) buildStructuredSeq ss
       joinPairs m nodes
buildStructuredSeq (A.Spec m (A.Specification mspec nm (A.Rep mrep rep)) str) route
  = let alter = AlterReplicator $ route22 (route33 (route23 route A.Spec) A.Specification) A.Rep in
    do n <- addNode' (findMeta rep) labelReplicator (nm, rep) alter
       (s,e) <- buildStructuredSeq str (route33 route A.Spec)
       addEdge ESeq n s
       addEdge ESeq e n
       return (n, n)
buildStructuredSeq (A.Spec m spec str) route
  = do (n,n') <- addSpecNodes spec route
       buildProcessOrFunctionSpec spec (route23 route A.Spec)
       (s,e) <- buildStructuredSeq str (route33 route A.Spec)
       addEdge ESeq n s
       addEdge ESeq e n'
       return (n, n')
buildStructuredSeq (A.Only _ p) route = buildProcess p (route22 route A.Only)
buildStructuredSeq (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       (ss, se) <- buildStructuredSeq str (route33 route A.ProcThen)
       addEdge ESeq pe ss
       return (ps, se)

buildStructuredPar :: (Monad mLabel, Monad mAlter) => Int -> (Node, Node) ->
  A.Structured A.Process -> ASTModifier mAlter (A.Structured A.Process) structType ->
  GraphMaker mLabel mAlter label structType (Either Bool (Node, Node))
buildStructuredPar pId (nStart, nEnd) (A.Several m ss) route
  = do nodes <- mapMRE (route22 route A.Several) (buildStructuredPar pId (nStart, nEnd)) ss
       addParEdges pId (nStart, nEnd) $ either (const []) id nodes
       return $ Left $ nonEmpty nodes
buildStructuredPar pId (nStart, nEnd) (A.Spec mstr (A.Specification mspec nm (A.Rep m rep)) str) route
  = let alter = AlterReplicator $ route22 (route33 (route23 route A.Spec) A.Specification) A.Rep in
    do s <- addNode' (findMeta rep) labelReplicator (nm, rep) alter
       e <- addDummyNode m
       pId' <- getNextParEdgeId
       nodes <- buildStructuredPar pId' (s,e) str (route33 route A.Spec)
       case nodes of
         Left False -> addEdge ESeq s e
         Left True -> return ()
         Right (s',e') -> do addEdge (EStartPar pId') s s'
                             addEdge (EEndPar pId') e' e
       return $ Right (s,e)
buildStructuredPar pId (nStart, nEnd) (A.Spec m spec str) route
  = do (n,n') <- addSpecNodes spec route
       pId' <- getNextParEdgeId
       buildProcessOrFunctionSpec spec (route23 route A.Spec)
       nodes <- buildStructuredPar pId' (n, n') str (route33 route A.Spec)
       case nodes of
         Left False -> do addEdge ESeq n n'
         Left True -> return ()
         Right (s,e) -> do addEdge ESeq n s
                           addEdge ESeq e n'
       return $ Right (n,n')
buildStructuredPar _ _ (A.Only _ p) route = buildProcess p (route22 route A.Only) >>* Right
buildStructuredPar pId (nStart, nEnd) (A.ProcThen m p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       n <- addDummyNode m
       pId' <- getNextParEdgeId
       nodes <- buildStructuredPar pId' (pe, n) str (route33 route A.ProcThen)
       case nodes of
         Left False -> return $ Right (ps, pe)
         Left True -> return $ Right (ps, n)
         Right (s,e) -> do addEdge ESeq pe s
                           return $ Right (ps, e)

buildStructuredCase :: (Monad mLabel, Monad mAlter) => (Node, Node) -> A.Structured A.Option -> ASTModifier mAlter (A.Structured A.Option) structType ->
  GraphMaker mLabel mAlter label structType ()
buildStructuredCase (nStart, nEnd) (A.Several _ ss) route
  = do mapMR (route22 route A.Several) (buildStructuredCase (nStart, nEnd)) ss
       return ()
buildStructuredCase (nStart, nEnd) (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       addEdge ESeq nStart ps
       buildStructuredCase (pe, nEnd) str (route33 route A.ProcThen)
buildStructuredCase (nStart, nEnd) (A.Only _ o) route
  = buildOnlyOption (nStart, nEnd) (route22 route A.Only) o
buildStructuredCase (nStart, nEnd) (A.Spec _ spec str) route
  = do (n, n') <- addSpecNodes spec route
       addEdge ESeq nStart n
       addEdge ESeq n' nEnd
       buildStructuredCase (n, n') str (route33 route A.Spec)

buildStructuredIf :: forall mLabel mAlter label structType. (Monad mLabel, Monad mAlter) => (Node, Node) -> A.Structured A.Choice -> ASTModifier mAlter (A.Structured A.Choice) structType ->
  GraphMaker mLabel mAlter label structType Node
buildStructuredIf (prev, end) (A.Several _ ss) route
  = foldM foldIf prev (zip [0..] ss)
      where
        foldIf :: Node -> (Int,A.Structured A.Choice) -> GraphMaker mLabel mAlter label structType Node
        foldIf prev (ind, s) = buildStructuredIf (prev, end) s $ route22 route A.Several @-> (routeList ind)
buildStructuredIf (prev, end) (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       addEdge ESeq prev ps
       buildStructuredIf (pe, end) str (route33 route A.ProcThen)
buildStructuredIf (prev, end) (A.Only _ c) route
  = buildOnlyChoice (prev, end) (route22 route A.Only) c
buildStructuredIf (prev, end) (A.Spec _ (A.Specification _ nm (A.Rep _ rep)) str) route
  = let alter = AlterReplicator $ route22 (route33 (route23 route A.Spec) A.Specification) A.Rep in
    do repNode <- addNode' (findMeta rep) labelReplicator (nm, rep) alter
       lastNode <- buildStructuredIf (repNode, end) str (route33 route A.Spec)
       addEdge ESeq prev repNode
       addEdge ESeq lastNode repNode
       return repNode
buildStructuredIf (prev, end) (A.Spec _ spec str) route
       -- Specs are tricky in IFs, because they can scope out either
       -- at the end of a choice-block, or when moving on to the next
       -- choice.  But these nodes are not the same because they have
       -- different connections leading out of them
  = do nIn <- addNode' (findMeta spec) labelScopeIn spec (AlterSpec $ route23 route A.Spec)
       nOutBlock <- addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)
       nOutNext <- addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)
       
       last <- buildStructuredIf (nIn, nOutBlock) str (route33 route A.Spec)
       
       addEdge ESeq prev nIn
       when (last /= prev) $ -- Only add the edge if there was a block it's connected to!
         addEdge ESeq nOutBlock end
       addEdge ESeq last nOutNext
       return nOutNext

buildOnlyChoice :: (Monad mLabel, Monad mAlter) => (Node, Node) -> ASTModifier mAlter A.Choice structType -> A.Choice -> GraphMaker mLabel mAlter label structType Node
buildOnlyChoice (cPrev, cEnd) route (A.Choice m exp p)
  = do nexp <- addNodeExpression (findMeta exp) exp $ route23 route A.Choice
       (nbodys, nbodye) <- buildProcess p $ route33 route A.Choice
       addEdge ESeq nexp nbodys
       addEdge ESeq cPrev nexp
       addEdge ESeq nbodye cEnd
       return nexp

buildOnlyOption :: (Monad mLabel, Monad mAlter) => (Node, Node) -> ASTModifier mAlter A.Option structType -> A.Option -> GraphMaker mLabel mAlter label structType ()
buildOnlyOption (cStart, cEnd) route opt
  = do (s,e) <-
         case opt of
           (A.Option m es p) -> do
             nexpNodes <- mapMR (route23 route A.Option) (\e r -> addNodeExpression (findMeta e) e r >>* mkPair) es
             (nexps, nexpe) <- joinPairs m nexpNodes
             (nbodys, nbodye) <- buildProcess p $ route33 route A.Option
             addEdge ESeq nexpe nbodys
             return (nexps,nbodye)
           (A.Else _ p) -> buildProcess p $ route22 route A.Else
       addEdge ESeq cStart s
       addEdge ESeq e cEnd
       return ()

buildOnlyAlternative :: (Monad mLabel, Monad mAlter) => ASTModifier mAlter A.Alternative structType -> A.Alternative ->
  GraphMaker mLabel mAlter label structType (Node, Node)
buildOnlyAlternative route alt
  = do let (m,p,r) = case alt of
              (A.Alternative m _ _ _ p) -> (m,p, route55 route A.Alternative)
              (A.AlternativeSkip m _ p) -> (m,p, route33 route A.AlternativeSkip)
       guardNode <- addNode' m labelAlternative alt (AlterAlternative route)
       (bodyNodeStart, bodyNodeEnd) <- buildProcess p r
       addEdge ESeq guardNode bodyNodeStart
       return (guardNode, bodyNodeEnd)

addNewSubProcFunc :: (Monad mLabel, Monad mAlter) => 
  Meta -> [A.Formal] -> Either (A.Process, ASTModifier mAlter A.Process structType) (A.Structured A.ExpressionList, ASTModifier mAlter (A.Structured A.ExpressionList) structType) ->
      ASTModifier mAlter [A.Formal] structType -> GraphMaker mLabel mAlter label structType ()
addNewSubProcFunc m args body argsRoute
  = do root <- addNode' m labelStartNode (m, args) (AlterArguments argsRoute)
       denoteRootNode root
       (bodyNode, termNode) <- case body of
         Left (p,route) -> buildProcess p route
         Right (s,route) -> buildStructuredEL s route
       denoteTerminatorNode termNode
       addEdge ESeq root bodyNode

buildProcess :: (Monad mLabel, Monad mAlter) => A.Process -> ASTModifier mAlter A.Process structType -> GraphMaker mLabel mAlter label structType (Node, Node)
buildProcess (A.Seq m s) route
  = buildStructuredSeq s (route22 route A.Seq)
buildProcess (A.Par m _ s) route
  = do nStart <- addDummyNode m
       nEnd <- addDummyNode m
       pId <- getNextParEdgeId
       nodes <- buildStructuredPar pId (nStart, nEnd) s (route33 route A.Par)
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
       buildStructuredCase (nStart,nEnd) s (route33 route A.Case)
       return (nStart, nEnd)
buildProcess (A.If m s) route
  = do nStart <- addDummyNode m
       nEnd <- addDummyNode m
       buildStructuredIf (nStart, nEnd) s (route22 route A.If)
       return (nStart, nEnd)
buildProcess (A.Alt m _ s) route
  = do nStart <- addDummyNode m
       nEnd <- addDummyNode m
       specNodes <- buildJustSpecs s (route33 route A.Alt)
       (nStart', nEnd') <- case specNodes of
         Just ((nInStart, nInEnd), (nOutStart, nOutEnd)) ->
           do addEdge ESeq nStart nInStart
              addEdge ESeq nOutEnd nEnd
              return (nInEnd, nOutStart)
         Nothing -> return (nStart, nEnd)
       buildStructuredAltNoSpecs (nStart', nEnd') s (route33 route A.Alt)
       return (nStart, nEnd)
buildProcess p route = addNode' (findMeta p) labelProcess p (AlterProcess route) >>* mkPair



-- | Builds a control-flow-graph.  The mAlter monad is the monad in which
-- AST alterations would take place.  Note that mAlter does not feature in
-- the parameters, only in the result.  The mLabel monad is the monad in
-- which the labelling must be done; hence the flow-graph is returned inside
-- the label monad.
--
-- Returns the flow graph, a list of start-roots and a list of terminator nodes
-- ("end-roots")
buildFlowGraph :: forall mLabel mAlter label. (Monad mLabel, Monad mAlter) =>
  GraphLabelFuncs mLabel label ->
  A.AST  ->
  mLabel (Either String (FlowGraph' mAlter label (), [Node], [Node]))
buildFlowGraph funcs s
  = do res <- flip runStateT (0, 0, ([],[]), [], []) $ flip runReaderT funcs $ runErrorT $ buildStructuredAST s id
       return $ case res of
                  (Left err,_) -> Left err
                  (Right _,(_,_,(nodes, edges),roots,terminators))
                    -> Right (mkGraph nodes edges, roots, terminators)

buildFlowGraphP :: forall mLabel mAlter label. (Monad mLabel, Monad mAlter) =>
  GraphLabelFuncs mLabel label ->
  A.Structured A.Process ->
  mLabel (Either String (FlowGraph' mAlter label A.Process, [Node], [Node]))
buildFlowGraphP funcs s
  = do res <- flip runStateT (0, 0, ([],[]), [], []) $ flip runReaderT funcs $ runErrorT $ buildStructuredSeq s id
       return $ case res of
                  (Left err,_) -> Left err
                  (Right (root,_),(_,_,(nodes, edges),roots, terminators))
                    -> Right (mkGraph nodes edges, root : roots, terminators)

    
