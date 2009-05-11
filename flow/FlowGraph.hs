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
import Data.Generics (Data)
import Data.Graph.Inductive hiding (run)
import Data.Maybe

import qualified AST as A
import CompState
import Data.Generics.Alloy.Route
import Metadata
import FlowUtils
import Utils

-- Helper for add a standard sequential edge:
(-->) :: (Monad mLabel, Monad mAlter) => Node -> Node -> GraphMaker mLabel mAlter label structType ()
(-->) = addEdge (ESeq Nothing)

addSpecNodes :: (Monad mAlter, Monad mLabel, Data a) => A.Specification -> ASTModifier mAlter (A.Structured a) structType -> GraphMaker mLabel mAlter label structType (Node, Node)
addSpecNodes spec route
  = do n <- addNode' (findMeta spec) labelScopeIn spec (AlterSpec $ route23 route A.Spec)
       n' <- addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)
       return (n, n')

-- Descends into process or function specifications, but doesn't join them up.  Any other specifications are ignored
buildProcessOrFunctionSpec :: (Monad mAlter, Monad mLabel) => A.Specification -> ASTModifier mAlter (A.Specification) structType ->
  GraphMaker mLabel mAlter label structType ()
buildProcessOrFunctionSpec (A.Specification _ _ (A.Proc m _ args (Just p))) route
 = let procRoute = (route33 route A.Specification) in
   addNewSubProcFunc m args (Left (p, route11 (route44 procRoute A.Proc) Just)) (route34 procRoute A.Proc)
buildProcessOrFunctionSpec (A.Specification _ _ (A.Function m _ _ args (Just es))) route
  = let funcRoute = (route33 route A.Specification) in
    case es of
      Left sel -> addNewSubProcFunc m args (Right (sel, route55 funcRoute A.Function @-> (makeRoute
        [0,0] $ \f (Just (Left e)) -> f e >>* (Just . Left)))) (route45 funcRoute A.Function)
      Right p -> addNewSubProcFunc m args (Left (p, route55 funcRoute A.Function @-> (makeRoute
        [0,0] $ \f (Just (Right p)) -> f p >>* (Just . Right)))) (route45 funcRoute A.Function)
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
       withDeclSpec spec $ buildStructuredAST str (route33 route A.Spec)
buildStructuredAST s _ = throwError $ "Unexpected element at top-level: " ++ show s

buildStructuredEL :: (Monad mLabel, Monad mAlter) => A.Structured A.ExpressionList -> ASTModifier mAlter (A.Structured A.ExpressionList) structType ->
  GraphMaker mLabel mAlter label structType (Node, Node)
buildStructuredEL (A.Only m el) route = addNodeExpressionList m el (route22 route A.Only) >>* mkPair
buildStructuredEL (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       (ss, se) <- buildStructuredEL str (route33 route A.ProcThen)
       pe --> ss
       return (ps, se)
buildStructuredEL (A.Spec m spec str) route
  = do (n,n') <- addSpecNodes spec route
       buildProcessOrFunctionSpec spec (route23 route A.Spec)
       (s,e) <- withDeclSpec spec $ buildStructuredEL str (route33 route A.Spec)
       n --> s
       e --> n'
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
buildStructuredAltNoSpecs se (A.Spec _ spec str) route = withDeclSpec spec $ buildStructuredAltNoSpecs se str (route33 route A.Spec)
buildStructuredAltNoSpecs se (A.Several m ss) route
  = mapMR (route22 route A.Several) (buildStructuredAltNoSpecs se) ss >> return ()
buildStructuredAltNoSpecs se (A.ProcThen _ _ str) route
  -- ProcThen is considered part of the specs, so we ignore it here
  = buildStructuredAltNoSpecs se str (route33 route A.ProcThen)
buildStructuredAltNoSpecs (nStart, nEnd) (A.Only _ guard) route
  = do (s,e) <- buildOnlyAlternative (route22 route A.Only) guard
       nStart --> s
       e --> nEnd

foldSpecs :: forall mAlter mLabel label structType. (Monad mLabel, Monad mAlter) => [Maybe ((Node, Node), (Node, Node))] -> GraphMaker mLabel mAlter label structType (Maybe ((Node, Node), (Node, Node)))
foldSpecs sps = case catMaybes sps of
    [] -> return Nothing
    (x:xs) -> foldM fold x xs >>* Just
  where
    fold :: ((Node, Node), (Node, Node)) -> ((Node, Node), (Node, Node)) -> GraphMaker mLabel mAlter label structType ((Node, Node), (Node, Node))
    fold ((inStartA, inEndA), (outStartA, outEndA)) ((inStartB, inEndB), (outStartB, outEndB))
      = do inEndA --> inStartB
           outEndB --> outStartA
           return ((inStartA, inEndB), (outStartB, outEndA))

buildJustSpecs :: (Monad mLabel, Monad mAlter, Data a) => A.Structured a -> ASTModifier mAlter (A.Structured a) structType ->
  GraphMaker mLabel mAlter label structType (Maybe ((Node, Node), (Node, Node)))
buildJustSpecs (A.Only {}) _ = return Nothing
buildJustSpecs (A.Several _ ss) route = mapMR (route22 route A.Several) buildJustSpecs ss >>= foldSpecs
buildJustSpecs (A.Spec _ spec str) route
  = do (scopeIn, scopeOut) <- addSpecNodes spec route
       inner <- withDeclSpec spec $ buildJustSpecs str (route33 route A.Spec)
       case inner of
         Nothing -> return $ Just ((scopeIn, scopeIn), (scopeOut, scopeOut))
         Just ((innerInStart, innerInEnd), (innerOutStart, innerOutEnd)) ->
           do scopeIn --> innerInStart
              innerOutEnd --> scopeOut
              return $ Just ((scopeIn, innerInEnd), (innerOutStart, scopeOut))
buildJustSpecs (A.ProcThen m p str) route
  = do inner <- buildJustSpecs str (route33 route A.ProcThen)
       (procNodeStart, procNodeEnd) <- buildProcess p (route23 route A.ProcThen)
       case inner of
         Nothing -> throwError "ProcThen was used without an inner specification"
         Just ((innerInStart, innerInEnd), innerOut) ->
           do procNodeEnd --> innerInStart
              return $ Just ((procNodeStart, innerInEnd), innerOut)

buildStructuredSeq :: (Monad mLabel, Monad mAlter) => A.Structured A.Process -> ASTModifier mAlter (A.Structured A.Process) structType ->
  GraphMaker mLabel mAlter label structType (Node, Node)
buildStructuredSeq (A.Several m ss) route
  = do nodes <- mapMR (route22 route A.Several) buildStructuredSeq ss
       joinPairs m route nodes
buildStructuredSeq (A.Spec m spec@(A.Specification mspec nm (A.Rep mrep rep)) str) route
  = let alter = AlterReplicator $ route22 (route33 (route23 route A.Spec) A.Specification) A.Rep in
    do n <- addNode' (findMeta rep) labelReplicator (nm, rep) alter
       (s,e) <- withDeclSpec spec $ buildStructuredSeq str (route33 route A.Spec)
       n --> s
       e --> n
       return (n, n)
buildStructuredSeq (A.Spec m spec str) route
  = do (n,n') <- addSpecNodes spec route
       buildProcessOrFunctionSpec spec (route23 route A.Spec)
       (s,e) <- withDeclSpec spec $ buildStructuredSeq str (route33 route A.Spec)
       n --> s
       e --> n'
       return (n, n')
buildStructuredSeq (A.Only _ p) route = buildProcess p (route22 route A.Only)
buildStructuredSeq (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       (ss, se) <- buildStructuredSeq str (route33 route A.ProcThen)
       pe --> ss
       return (ps, se)

buildStructuredPar :: (Monad mLabel, Monad mAlter) => Integer -> (Node, Node) ->
  A.Structured A.Process -> ASTModifier mAlter (A.Structured A.Process) structType ->
  GraphMaker mLabel mAlter label structType (Either Bool (Node, Node))
buildStructuredPar pId (nStart, nEnd) (A.Several m ss) route
  = do nodes <- mapMRE (route22 route A.Several) (buildStructuredPar pId (nStart, nEnd)) ss
       addParEdges pId (nStart, nEnd) $ either (const []) id nodes
       return $ Left $ nonEmpty nodes
buildStructuredPar pId (nStart, nEnd) (A.Spec mstr spec@(A.Specification mspec nm (A.Rep m rep)) str) route
  = let alter = AlterReplicator $ route22 (route33 (route23 route A.Spec) A.Specification) A.Rep in
    do s <- addNode' (findMeta rep) labelReplicator (nm, rep) alter
       e <- addDummyNode m route
       pId' <- getNextParEdgeId
       nodes <- withDeclSpec spec $ buildStructuredPar pId' (s,e) str (route33 route A.Spec)
       case nodes of
         Left False -> s --> e
         Left True -> return ()
         Right (s',e') -> do addEdge (EStartPar pId') s s'
                             addEdge (EEndPar pId') e' e
       return $ Right (s,e)
buildStructuredPar pId (nStart, nEnd) (A.Spec m spec str) route
  = do (n,n') <- addSpecNodes spec route
       pId' <- getNextParEdgeId
       buildProcessOrFunctionSpec spec (route23 route A.Spec)
       nodes <- withDeclSpec spec $ buildStructuredPar pId' (n, n') str (route33 route A.Spec)
       case nodes of
         Left False -> n --> n'
         Left True -> return ()
         Right (s,e) -> do n --> s
                           e --> n'
       return $ Right (n,n')
buildStructuredPar _ _ (A.Only _ p) route = buildProcess p (route22 route A.Only) >>* Right
buildStructuredPar pId (nStart, nEnd) (A.ProcThen m p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       n <- addDummyNode m route
       pId' <- getNextParEdgeId
       nodes <- buildStructuredPar pId' (pe, n) str (route33 route A.ProcThen)
       case nodes of
         Left False -> return $ Right (ps, pe)
         Left True -> return $ Right (ps, n)
         Right (s,e) -> do pe --> s
                           return $ Right (ps, e)

buildStructuredCase :: (Monad mLabel, Monad mAlter) => (Node, Node) -> A.Structured A.Option -> ASTModifier mAlter (A.Structured A.Option) structType ->
  GraphMaker mLabel mAlter label structType ()
buildStructuredCase (nStart, nEnd) (A.Several _ ss) route
  = do mapMR (route22 route A.Several) (buildStructuredCase (nStart, nEnd)) ss
       return ()
buildStructuredCase (nStart, nEnd) (A.ProcThen _ p str) route
  = do (ps, pe) <- buildProcess p (route23 route A.ProcThen)
       nStart --> ps
       buildStructuredCase (pe, nEnd) str (route33 route A.ProcThen)
buildStructuredCase (nStart, nEnd) (A.Only _ o) route
  = buildOnlyOption (nStart, nEnd) (route22 route A.Only) o
buildStructuredCase (nStart, nEnd) (A.Spec _ spec str) route
  = do (n, n') <- addSpecNodes spec route
       nStart --> n
       n' --> nEnd
       withDeclSpec spec $ buildStructuredCase (n, n') str (route33 route A.Spec)

-- While building an IF, we keep a stack of identifiers used for the various conditionals.
--  At the end of the block you must make sure there are edges that terminate all
-- these identifiers, after the joining together of all the branches
buildStructuredIf :: forall mLabel mAlter label structType. (Monad mLabel, Monad mAlter) => (Node, Node) -> A.Structured A.Choice -> ASTModifier mAlter (A.Structured A.Choice) structType ->
  StateT [Integer] (GraphMaker mLabel mAlter label structType) Node
buildStructuredIf (prev, end) (A.Several _ ss) route
  = foldM foldIf prev (zip [0..] ss)
      where
        foldIf :: Node -> (Int,A.Structured A.Choice) ->
          StateT [Integer] (GraphMaker mLabel mAlter label structType) Node
        foldIf prev (ind, s) = buildStructuredIf (prev, end) s $ route22 route A.Several @-> (routeList ind)
buildStructuredIf (prev, end) (A.ProcThen _ p str) route
  = do (ps, pe) <- lift $ buildProcess p (route23 route A.ProcThen)
       lift $ prev --> ps
       buildStructuredIf (pe, end) str (route33 route A.ProcThen)
buildStructuredIf (prev, end) (A.Only _ c) route
  = do id <- lift getNextParEdgeId
       modify (id:)
       lift $ buildOnlyChoice (prev, end) (route22 route A.Only) c id
buildStructuredIf (prev, end) (A.Spec _ spec@(A.Specification _ nm (A.Rep _ rep)) str) route
  = let alter = AlterReplicator $ route22 (route33 (route23 route A.Spec) A.Specification) A.Rep in
    do repNode <- lift $ addNode' (findMeta rep) labelReplicator (nm, rep) alter
       lastNode <- liftWrapStateT (withDeclSpec spec) $ buildStructuredIf (repNode, end) str (route33 route A.Spec)
       lift $ prev --> repNode
       lift $ lastNode --> repNode
       return repNode
buildStructuredIf (prev, end) (A.Spec _ spec str) route
       -- Specs are tricky in IFs, because they can scope out either
       -- at the end of a choice-block, or when moving on to the next
       -- choice.  But these nodes are not the same because they have
       -- different connections leading out of them
  = do nIn <- lift $ addNode' (findMeta spec) labelScopeIn spec (AlterSpec $ route23 route A.Spec)
       nOutBlock <- lift $ addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)
       nOutNext <- lift $ addNode' (findMeta spec) labelScopeOut spec (AlterSpec $ route23 route A.Spec)
       
       last <- liftWrapStateT (withDeclSpec spec) $ buildStructuredIf (nIn, nOutBlock) str (route33 route A.Spec)
       lift $ do
         prev --> nIn
         when (last /= prev) $ -- Only add the edge if there was a block it's connected to!
           nOutBlock --> end
         last --> nOutNext
         return nOutNext

buildOnlyChoice :: (Monad mLabel, Monad mAlter) => (Node, Node) -> ASTModifier mAlter A.Choice structType -> A.Choice ->
  Integer -> GraphMaker mLabel mAlter label structType Node
buildOnlyChoice (cPrev, cEnd) route (A.Choice m exp p) edgeId
  = do nexp <- addNode' (findMeta exp) labelConditionalExpression exp
                 $ AlterExpression $ route23 route A.Choice
       nexpf <- addDummyNode m route
       (nbodys, nbodye) <- buildProcess p $ route33 route A.Choice
       cPrev --> nexp
       addEdge (ESeq $ Just (edgeId, Just True)) nexp nbodys
       addEdge (ESeq $ Just (edgeId, Just False)) nexp nexpf
       nbodye --> cEnd
       return nexpf

buildOnlyOption :: (Monad mLabel, Monad mAlter) => (Node, Node) -> ASTModifier mAlter A.Option structType -> A.Option -> GraphMaker mLabel mAlter label structType ()
buildOnlyOption (cStart, cEnd) route opt
  = do (s,e) <-
         case opt of
           (A.Option m es p) -> do
             nexpNodes <- mapMR (route23 route A.Option) (\e r -> addNodeExpression (findMeta e) e r >>* mkPair) es
             (nexps, nexpe) <- joinPairs m route nexpNodes
             (nbodys, nbodye) <- buildProcess p $ route33 route A.Option
             nexpe --> nbodys
             return (nexps,nbodye)
           (A.Else _ p) -> buildProcess p $ route22 route A.Else
       cStart --> s
       e --> cEnd
       return ()

buildOnlyAlternative :: (Monad mLabel, Monad mAlter) => ASTModifier mAlter A.Alternative structType -> A.Alternative ->
  GraphMaker mLabel mAlter label structType (Node, Node)
buildOnlyAlternative route alt
  = do let (m,p,r) = case alt of
              (A.Alternative m _ _ _ p) -> (m,p, route55 route A.Alternative)
              (A.AlternativeSkip m _ p) -> (m,p, route33 route A.AlternativeSkip)
              -- TODO label the pre-conditions, and use separate nodes for
              -- them
       guardNode <- addNode' m labelAlternative alt (AlterAlternative route)
       (bodyNodeStart, bodyNodeEnd) <- buildProcess p r
       guardNode --> bodyNodeStart
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
       root --> bodyNode

buildProcess :: (Monad mLabel, Monad mAlter) => A.Process -> ASTModifier mAlter A.Process structType -> GraphMaker mLabel mAlter label structType (Node, Node)
buildProcess (A.Seq m s) route
  = buildStructuredSeq s (route22 route A.Seq)
buildProcess (A.Par m _ s) route
  = do nStart <- addDummyNode m route
       nEnd <- addDummyNode m route
       pId <- getNextParEdgeId
       nodes <- buildStructuredPar pId (nStart, nEnd) s (route33 route A.Par)
       case nodes of
         Left False -> nStart --> nEnd -- no processes in PAR, join start and end with simple ESeq link
         Left True -> return () -- already wired up
         Right (start, end) ->
              do addEdge (EStartPar pId) nStart start
                 addEdge (EEndPar pId) end nEnd
       return (nStart, nEnd)
buildProcess (A.While m e p) route
  = do n <- addNode' (findMeta e) labelConditionalExpression e (AlterExpression
         $ route23 route A.While)
       nAfter <- addDummyNode m route
       (start, end) <- buildProcess p (route33 route A.While)
       edgeId <- getNextParEdgeId
       addEdge (ESeq $ Just (edgeId, Just True)) n start
       addEdge (ESeq $ Just (edgeId, Just False)) n nAfter
       addEdge (ESeq $ Just (edgeId, Nothing)) end n
       -- We are still taking the condition to be true after the while loop --
       -- and it will remain so until the variables are later modified
       return (n, nAfter)
buildProcess (A.Case m e s) route
  = do nStart <- addNodeExpression (findMeta e) e (route23 route A.Case)
       nEnd <- addDummyNode m route
       buildStructuredCase (nStart,nEnd) s (route33 route A.Case)
       return (nStart, nEnd)
buildProcess (A.If m s) route
  = do nStart <- addDummyNode m route
       nFirstEnd <- addDummyNode m route
       allEdgeIds <- flip execStateT [] $ buildStructuredIf (nStart, nFirstEnd) s (route22 route A.If)
       nLastEnd <- foldM addEndEdge nFirstEnd allEdgeIds
       return (nStart, nLastEnd)
  where
    --addEndEdge :: Node -> Integer -> GraphMaker mLabel mAlter label structType Node
    addEndEdge n id = do n' <- addDummyNode m route
                         addEdge (ESeq (Just (id, Nothing))) n n'
                         return n'
buildProcess (A.Alt m _ s) route
  = do nStart <- addDummyNode m route
       nEnd <- addDummyNode m route
       specNodes <- buildJustSpecs s (route33 route A.Alt)
       (nStart', nEnd') <- case specNodes of
         Just ((nInStart, nInEnd), (nOutStart, nOutEnd)) ->
           do nStart --> nInStart
              nOutEnd --> nEnd
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
  = do res <- flip runStateT (GraphMakerState 0 0 ([],[]) [] [] []) $ flip runReaderT funcs $ runErrorT $ buildStructuredAST s identityRoute
       return $ case res of
                  (Left err,_) -> Left err
                  (Right _,GraphMakerState _ _ (nodes, edges) roots terminators _)
                    -> Right (mkGraph nodes edges, roots, terminators)

buildFlowGraphP :: forall mLabel mAlter label. (Monad mLabel, Monad mAlter) =>
  GraphLabelFuncs mLabel label ->
  A.Structured A.Process ->
  mLabel (Either String (FlowGraph' mAlter label A.Process, [Node], [Node]))
buildFlowGraphP funcs s
  = do res <- flip runStateT (GraphMakerState 0 0 ([],[]) [] [] []) $ flip runReaderT funcs $ runErrorT $ buildStructuredSeq s identityRoute
       return $ case res of
                  (Left err,_) -> Left err
                  (Right (root,_),GraphMakerState _ _ (nodes, edges) roots terminators _)
                    -> Right (mkGraph nodes edges, root : roots, terminators)

    
