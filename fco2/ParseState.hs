-- | Compiler state.
module ParseState where

import Data.Generics
import Control.Monad.State

import qualified AST as A
import Metadata

data Flag = ParseOnly | Verbose | Debug
  deriving (Eq, Show, Data, Typeable)

-- | State necessary for compilation.
data ParseState = ParseState {
    -- Set by Main
    psFlags :: [Flag],

    -- Set by Parse
    psLocalNames :: [(String, A.Name)],
    psNames :: [(String, A.NameDef)],
    psNameCounter :: Int,
    psConstants :: [(String, A.Expression)],

    -- Set by passes
    psNonceCounter :: Int,
    psFunctionReturns :: [(String, [A.Type])],
    psPulledItems :: [A.Process -> A.Process],
    psAdditionalArgs :: [(String, [A.Actual])],
    psMainName :: Maybe A.Name
  }
  deriving (Show, Data, Typeable)

instance Show (A.Process -> A.Process) where
  show p = "(function on A.Process)"

emptyState :: ParseState
emptyState = ParseState {
    psFlags = [],

    psLocalNames = [],
    psNames = [],
    psNameCounter = 0,
    psConstants = [],

    psNonceCounter = 0,
    psFunctionReturns = [],
    psPulledItems = [],
    psAdditionalArgs = [],
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
          return $ A.Specification m n st

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: MonadState ParseState m => Meta -> A.Process -> m A.Specification
makeNonceProc m p
    = defineNonce m "wrapper_proc" (A.Proc m [] p) A.ProcName A.Abbrev

-- | Generate and define a variable abbreviation.
makeNonceIs :: MonadState ParseState m => String -> Meta -> A.Type -> A.AbbrevMode -> A.Variable -> m A.Specification
makeNonceIs s m t am v
    = defineNonce m s (A.Is m am t v) A.VariableName am

-- | Generate and define an expression abbreviation.
makeNonceIsExpr :: MonadState ParseState m => String -> Meta -> A.Type -> A.Expression -> m A.Specification
makeNonceIsExpr s m t e
    = defineNonce m s (A.IsExpr m A.ValAbbrev t e) A.VariableName A.ValAbbrev

-- | Generate and define a variable.
makeNonceVariable :: MonadState ParseState m => String -> Meta -> A.Type -> A.NameType -> A.AbbrevMode -> m A.Specification
makeNonceVariable s m t nt am
    = defineNonce m s (A.Declaration m t) nt am

-- | Is a name on the list of constants?
isConstantName :: ParseState -> A.Name -> Bool
isConstantName ps n
    = case lookup (A.nameName n) (psConstants ps) of
        Just _ -> True
        Nothing -> False

