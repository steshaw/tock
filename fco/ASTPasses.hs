-- Parses across the AST

module ASTPasses (astPasses) where

import qualified AST as A
import Data.Generics
import Control.Monad.State

astPasses =
  [ ("Silly monad example", numberPass)
  ]

number :: A.Name -> State Int A.Name
number (A.Name s) = do
  i <- get
  put (i + 1)
  return $ A.Name (s ++ "." ++ (show i))

numberPass :: A.Process -> A.Process
numberPass n = evalState (everywhereM (mkM number) n) 0

