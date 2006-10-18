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

    withNames :: Data t => [A.Name] -> t -> UniqueM ([A.Name], t)
    withNames ns b = do
      (count, vars) <- get
      let names = [s | A.Name s <- ns]
      let names' = [n ++ "." ++ show (count + i) | (n, i) <- zip names [0..]]
      put (count + length ns, (zip names names') ++ vars)

      b' <- doAny b

      (count', _) <- get
      put (count', vars)

      return (map A.Name names', b')

    withName :: Data t => A.Name -> t -> UniqueM (A.Name, t)
    withName n b = do
      (n':[], b') <- withNames [n] b
      return (n', b')

    withFormals :: Data t => A.Formals -> t -> UniqueM (A.Formals, t)
    withFormals fs b = do
      (fns', b') <- withNames (map snd fs) b
      ts' <- mapM doAny (map fst fs)
      return (zip ts' fns', b')

    withSpec :: Data t => A.Specification -> t -> UniqueM (A.Specification, t)
    withSpec (n, st) b = do
      st' <- case st of
        A.Proc fs pp -> do (fs', pp') <- withFormals fs pp
                           return $ A.Proc fs' pp'
        A.Function rt fs pp -> do (fs', pp') <- withFormals fs pp
                                  return $ A.Function rt fs' pp'
        otherwise -> doAny st
      (n', b') <- withName n b
      return ((n', st'), b')

    withRep :: Data t => A.Replicator -> t -> UniqueM (A.Replicator, t)
    withRep (A.For n f1 f2) b = do
      (n', b') <- withName n b
      f1' <- doAny f1
      f2' <- doAny f2
      return $ (A.For n' f1' f2', b')

    doProcess :: A.Process -> UniqueM A.Process
    doProcess p = case p of
      A.ProcSpec s b -> do (s', b') <- withSpec s b
                           return $ A.ProcSpec s' b'
      A.SeqRep r b -> do (r', b') <- withRep r b
                         return $ A.SeqRep r' b'
      A.ParRep pri r b -> do (r', b') <- withRep r b
                             return $ A.ParRep pri r' b'
      otherwise -> doGeneric p

    doValueProcess :: A.ValueProcess -> UniqueM A.ValueProcess
    doValueProcess p = case p of
      A.ValOfSpec s b -> do (s', b') <- withSpec s b
                            return $ A.ValOfSpec s' b'
      otherwise -> doGeneric p

    doStructured :: A.Structured -> UniqueM A.Structured
    doStructured p = case p of
      A.Rep r b -> do (r', b') <- withRep r b
                      return $ A.Rep r' b'
      A.Spec s b -> do (s', b') <- withSpec s b
                       return $ A.Spec s' b'
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

