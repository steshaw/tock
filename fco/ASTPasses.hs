-- Parses across the AST

module ASTPasses (astPasses) where

import qualified AST as A
import Data.Generics
import Control.Monad.State

{- FIXME: Passes to add:
calculate types
fix Infer types
resolve "c ! x; y" ambiguity (is x tag or variable?)
resolve "x[y]" ambiguity (is y expression or tag?)
check types
add reference markers where appropriate
turn inline VALOFs into regular FUNCTIONs
identify free variables
rewrite PROC/FUNCTION declarations and uses to take free variables as parameters
make Names unique
make Names C-styled
mark Tags with their associated types
extract type/PROC/FUNCTION declarations
check only Main is left
-}

astPasses =
  [ ("C-style names", cStyleNamesPass)
  ]

{-
numberPass :: A.Process -> A.Process
numberPass n = evalState (everywhereM (mkM (number `extM` number')) n) 0
  where
    number :: A.Name -> State Int A.Name
    number (A.Name s) = do
      i <- get
      put (i + 1)
      return $ A.Name (s ++ "." ++ (show i))

    number' :: A.Tag -> State Int A.Tag
    number' (A.Tag s) = do
      i <- get
      put (i + 1)
      return $ A.Tag (s ++ "." ++ (show i))
-}

cStyleNamesPass :: A.Process -> A.Process
cStyleNamesPass = everywhere (mkT doName)
  where
    doName :: A.Name -> A.Name
    doName (A.Name s) = A.Name [if c == '.' then '_' else c | c <- s]

