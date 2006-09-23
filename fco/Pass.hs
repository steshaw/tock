-- Defining passes on the tree

module Pass where

import Tree

type Progress = (String -> IO ())

-- This is actually a fraction of a pass: an operation upon the tree.
-- The arguments are:
-- - "next": the next pass to try if this one doesn't match;
-- - "top": the pass to use recursively on subnodes;
-- - the input node.
type Pass = (Node -> Node) -> (Node -> Node) -> Node -> Node

runPasses :: [Pass] -> Node -> Node
runPasses passes = top
  where
    fail :: Node -> Node
    fail n = error $ "No match for node: " ++ (show n)

    makePassList :: [Pass] -> [Node -> Node]
    makePassList (p:[]) = [p fail top]
    makePassList (p:ps) = p (head rest) top : rest
      where rest = makePassList ps

    passList :: [Node -> Node]
    passList = makePassList passes

    top :: Node -> Node
    top = head passList

data Phase = Phase String [Pass] [(String, Pass)]

runPhase :: Phase -> Node -> Progress -> IO Node
runPhase (Phase name bases passes) n progress = do
  progress $ "Phase: " ++ name
  runPhase' (reverse passes) n
  where
    runPhase' :: [(String, Pass)] -> Node -> IO Node
    runPhase' [] n = do return n
    runPhase' ((name, p):ps) n = do rest <- runPhase' ps n
                                    progress $ "  Pass: " ++ name
                                    return $ runPasses (p : bases) rest

