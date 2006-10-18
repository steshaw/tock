-- Parses across the AST

--module ASTPasses (astPasses) where
module ASTPasses where

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

type UniqueState = (Int, [(String, String)])
type UniqueM t = State UniqueState t

uniqueNamesPass :: A.Process -> A.Process
uniqueNamesPass p = evalState (doAny p) (0, [])
  where
    doAny :: Data t => t -> UniqueM t
    doAny = doGeneric `extM` doName `extM` doProcess `extM` doValueProcess `extM` doStructured

    doGeneric :: Data t => t -> UniqueM t
    doGeneric = gmapM doAny

-- this is wrong for "v IS v:" -- name shouldn't come into scope until after the spec
    withSpec :: Data t => A.Specification -> t -> UniqueM t
    withSpec (A.Name n, _) p = do
      (_, vars) <- get
      (count, vars) <- get
      put (count + 1, (n, n ++ "." ++ show count) : vars)
      p' <- doGeneric p
      (count', _) <- get
      put (count', vars)
      return p'

    doProcess :: A.Process -> UniqueM A.Process
    doProcess p = case p of
      A.ProcSpec s _ -> withSpec s p
      otherwise -> doGeneric p

    doValueProcess :: A.ValueProcess -> UniqueM A.ValueProcess
    doValueProcess p = case p of
      A.ValOfSpec s _ -> withSpec s p
      otherwise -> doGeneric p

    doStructured :: A.Structured -> UniqueM A.Structured
    doStructured p = case p of
      A.Spec s _ -> withSpec s p
      otherwise -> doGeneric p

    doName :: A.Name -> UniqueM A.Name
    doName (A.Name s) = do
      (_, vars) <- get
      let s' = case lookup s vars of
                 Just n -> n
                 Nothing -> "(not-declared-" ++ s ++ ")"
                 --Nothing -> error $ "Name " ++ s ++ " not declared before use"
      return $ A.Name s'

cStyleNamesPass :: A.Process -> A.Process
cStyleNamesPass = everywhere (mkT doName)
  where
    doName :: A.Name -> A.Name
    doName (A.Name s) = A.Name [if c == '.' then '_' else c | c <- s]

