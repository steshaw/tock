-- Parses across the AST

module ASTPasses (astPasses) where

import qualified AST as A
import List
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
  [ ("Unique names", uniqueNamesPass)
  , ("C-style names", cStyleNamesPass)
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

type Transform t = t -> t

everyContext :: Data a => (forall b. Data b => (c, b) -> (c, b)) -> c -> a -> a
everyContext f c x = gmapT innerT x'
  where
    (c', x') = f (c, x)
    innerT xi = everyContext f c' xi

uniqueNamesPass :: Transform A.Process
uniqueNamesPass n = everyContext doAny [] n
  where
    doAny :: Data t => Transform ([String], t)
    doAny = (mkT doP) `extT` doV `extT` doS `extT` doN
    doP :: Transform ([String], A.Process)
    doP (c, p) = case p of
      A.ProcSpec ((A.Name n), _) _ -> (n : c, p)
      otherwise -> (c, p)
    doV :: Transform ([String], A.ValueProcess)
    doV = undefined
    doS :: Transform ([String], A.Structured)
    doS = undefined
    doN :: Transform ([String], A.Name)
    doN (c, A.Name s) = (c, A.Name (s ++ "=" ++ (concat $ intersperse "," c)))

cStyleNamesPass :: A.Process -> A.Process
cStyleNamesPass = everywhere (mkT doName)
  where
    doName :: A.Name -> A.Name
    doName (A.Name s) = A.Name [if c == '.' then '_' else c | c <- s]

