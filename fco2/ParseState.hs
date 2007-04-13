-- | Compiler state.
module ParseState where

import Data.Generics
import Control.Monad.State

import qualified AST as A
import Metadata

-- FIXME This is a rather inappropriate name now...
-- | State necessary for compilation.
data ParseState = ParseState {
    psLocalNames :: [(String, A.Name)],
    psNames :: [(String, A.NameDef)],
    psNameCounter :: Int,
    psNonceCounter :: Int,
    psPulledItems :: [A.Process -> A.Process],
    psMainName :: Maybe A.Name
  }
  deriving (Show, Data, Typeable)

instance Show (A.Process -> A.Process) where
  show p = "(function on A.Process)"

emptyState :: ParseState
emptyState = ParseState {
    psLocalNames = [],
    psNames = [],
    psNameCounter = 0,
    psNonceCounter = 0,
    psPulledItems = [],
    psMainName = Nothing
  }

-- | Add the definition of a name.
psDefineName :: A.Name -> A.NameDef -> ParseState -> ParseState
psDefineName n nd ps = ps { psNames = (A.nameName n, nd) : psNames ps }

-- | Find the definition of a name.
psLookupName :: ParseState -> A.Name -> Maybe A.NameDef
psLookupName ps n = lookup (A.nameName n) (psNames ps)

-- | Generate a throwaway unique name.
makeNonce :: MonadState ParseState m => String -> m String
makeNonce s
    =  do ps <- get
          let i = psNonceCounter ps
          put ps { psNonceCounter = i + 1 }
          return $ s ++ "_n" ++ show i

-- | Add a pulled item to the collection.
addPulled :: MonadState ParseState m => (A.Process -> A.Process) -> m ()
addPulled item
    =  do ps <- get
          put $ ps { psPulledItems = item : psPulledItems ps }

-- | Apply pulled items to a Process.
applyPulled :: MonadState ParseState m => A.Process -> m A.Process
applyPulled ast
    =  do ps <- get
          let ast' = foldl (\p f -> f p) ast (psPulledItems ps)
          put $ ps { psPulledItems = [] }
          return ast'

-- | Generate and define a nonce specification.
defineNonce :: MonadState ParseState m => Meta -> String -> A.SpecType -> A.NameType -> A.AbbrevMode -> m A.Specification
defineNonce m s st nt am
    =  do ns <- makeNonce s
          let n = A.Name m A.ProcName ns
          let nd = A.NameDef {
                     A.ndMeta = m,
                     A.ndName = ns,
                     A.ndOrigName = ns,
                     A.ndNameType = nt,
                     A.ndType = st,
                     A.ndAbbrevMode = am
                   }
          modify $ psDefineName n nd
          return (n, st)

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: MonadState ParseState m => Meta -> A.Process -> m A.Specification
makeNonceProc m p
    = defineNonce m "wrapper_proc" (A.Proc m [] p) A.ProcName A.Abbrev

-- | Generate and define a variable abbreviation.
makeNonceIs :: MonadState ParseState m => Meta -> A.Type -> A.AbbrevMode -> A.Variable -> m A.Specification
makeNonceIs m t am v
    = defineNonce m "var" (A.Is m am t v) A.VariableName am

-- | Generate and define an expression abbreviation.
makeNonceIsExpr :: MonadState ParseState m => Meta -> A.Type -> A.Expression -> m A.Specification
makeNonceIsExpr m t e
    = defineNonce m "expr" (A.IsExpr m A.ValAbbrev t e) A.VariableName A.ValAbbrev

