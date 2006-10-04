-- Defining and running passes across some type of tree

module Pass where

import Control.Monad.State

type Progress = (String -> IO ())

type Pass t = t -> t

type PassList t = [(String, Pass t)]

runPasses :: Show t => PassList t -> Progress -> t -> IO t
runPasses [] _ d = return d
runPasses ((name, pass):ps) progress d = do
  progress $ "{{{ Pass: " ++ name
  let d' = pass d
  progress $ show d'
  progress $ "}}}"
  runPasses ps progress d'

