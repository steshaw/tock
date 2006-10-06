-- How to "scrap my boilerplate"...

module Test where

import qualified Tree as N
import Data.Generics
import Control.Monad.State

number :: N.Node -> State Int N.Node
number (N.Name s) = do
  i <- get
  put (i + 1)
  return $ N.Name (s ++ "." ++ (show i))
number n = return n

numberPass :: N.Node -> N.Node
numberPass n = evalState (everywhereM (mkM number) n) 0

