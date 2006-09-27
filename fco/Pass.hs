-- Defining passes on the tree

module Pass where

import Tree
import Control.Monad.State

type Progress = (String -> IO ())

type ITransform st = Node -> State st Node
-- This is actually a fraction of a pass: an operation upon the tree.
-- The arguments are:
-- - "next": the next pass to try if this one doesn't match;
-- - "top": the pass to use recursively on subnodes;
-- - the input node.
type Transform st = ITransform st -> ITransform st -> ITransform st

runTransforms :: st -> [Transform st] -> Node -> Node
runTransforms initState passes node = evalState (top node) initState
  where
    fail :: ITransform st
    fail n = error $ "No match for node: " ++ (show n)

    makeTransformList (p:[]) = [p fail top]
    makeTransformList (p:ps) = p (head rest) top : rest
      where rest = makeTransformList ps

    passList = makeTransformList passes

    top = head passList

type Pass = Node -> Node

makePass :: st -> Transform st -> [Transform st] -> Pass
makePass initState t bases = runTransforms initState (t : bases)

data Phase = Phase String [(String, Pass)]

runPhase :: Phase -> Node -> Progress -> IO Node
runPhase (Phase name passes) n progress = do
  progress $ "Phase: " ++ name
  runPhase' (reverse passes) n
  where
    runPhase' :: [(String, Pass)] -> Node -> IO Node
    runPhase' [] n = do return n
    runPhase' ((name, pass):passes) n = do
      rest <- runPhase' passes n
      progress $ "  Pass: " ++ name
      return $ pass rest

