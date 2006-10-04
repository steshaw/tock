-- Defining and running passes across some type of tree

module Pass where

import Control.Monad.State
import Data.Generics
import PrettyShow

type Progress = (String -> IO ())

type Pass t = t -> t

type PassList t = [(String, Pass t)]

runPasses :: Data t => PassList t -> Progress -> t -> IO t
runPasses [] _ d = return d
runPasses ((name, pass):ps) progress d = do
  progress $ "{{{ Pass: " ++ name
  let d' = pass d
  progress $ pshow d'
  progress $ "}}}"
  runPasses ps progress d'

