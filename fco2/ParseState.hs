-- | Compiler state.
module ParseState where

import Data.Generics
import Control.Monad.State

import qualified AST as A
import Errors
import Metadata

-- | State necessary for compilation.
data ParseState = ParseState {
    -- Set by Main (from command-line options)
    psVerboseLevel :: Int,
    psParseOnly :: Bool,
    psOutputFile :: String,

    -- Set by preprocessor
    psSourceFiles :: [(String, String)],
    psIndentLinesIn :: [String],
    psIndentLinesOut :: [String],

    -- Set by Parse
    psLocalNames :: [(String, A.Name)],
    psMainLocals :: [(String, A.Name)],
    psNames :: [(String, A.NameDef)],
    psNameCounter :: Int,
    psTypeContext :: [Maybe A.Type],
    psLoadedFiles :: [String],
    psWarnings :: [String],

    -- Set by passes
    psNonceCounter :: Int,
    psFunctionReturns :: [(String, [A.Type])],
    psPulledItems :: [A.Process -> A.Process],
    psAdditionalArgs :: [(String, [A.Actual])]
  }
  deriving (Show, Data, Typeable)

instance Show (A.Process -> A.Process) where
  show p = "(function on A.Process)"

emptyState :: ParseState
emptyState = ParseState {
    psVerboseLevel = 0,
    psParseOnly = False,
    psOutputFile = "-",

    psSourceFiles = [],
    psIndentLinesIn = [],
    psIndentLinesOut = [],

    psLocalNames = [],
    psMainLocals = [],
    psNames = [],
    psNameCounter = 0,
    psTypeContext = [],
    psLoadedFiles = [],
    psWarnings = [],

    psNonceCounter = 0,
    psFunctionReturns = [],
    psPulledItems = [],
    psAdditionalArgs = []
  }

-- | Class of monads which keep a ParseState.
-- (This is just shorthand for the equivalent MonadState constraint.)
class MonadState ParseState m => PSM m
instance MonadState ParseState m => PSM m

-- | Add the definition of a name.
defineName :: PSM m => A.Name -> A.NameDef -> m ()
defineName n nd = modify $ (\ps -> ps { psNames = (A.nameName n, nd) : psNames ps })

-- | Find the definition of a name.
lookupName :: (PSM m, Die m) => A.Name -> m A.NameDef
lookupName n
    =  do ps <- get
          case lookup (A.nameName n) (psNames ps) of
            Just nd -> return nd
            Nothing -> die $ "cannot find name " ++ A.nameName n

-- | Add a warning.
addWarning :: PSM m => Meta -> String -> m ()
addWarning m s = modify (\ps -> ps { psWarnings = msg : psWarnings ps })
  where msg = "Warning: " ++ show m ++ ": " ++ s

-- | Generate a throwaway unique name.
makeNonce :: PSM m => String -> m String
makeNonce s
    =  do ps <- get
          let i = psNonceCounter ps
          put ps { psNonceCounter = i + 1 }
          return $ s ++ "_n" ++ show i

-- | Add a pulled item to the collection.
addPulled :: PSM m => (A.Process -> A.Process) -> m ()
addPulled item = modify (\ps -> ps { psPulledItems = item : psPulledItems ps })

-- | Apply pulled items to a Process.
applyPulled :: PSM m => A.Process -> m A.Process
applyPulled ast
    =  do ps <- get
          let ast' = foldl (\p f -> f p) ast (psPulledItems ps)
          put $ ps { psPulledItems = [] }
          return ast'

-- | Enter a type context.
pushTypeContext :: PSM m => Maybe A.Type -> m ()
pushTypeContext t
    = modify (\ps -> ps { psTypeContext = t : psTypeContext ps })

-- | Leave a type context.
popTypeContext :: PSM m => m ()
popTypeContext
    = modify (\ps -> ps { psTypeContext = tail $ psTypeContext ps })

-- | Get the current type context (or the given default value if there isn't one).
getTypeContext :: PSM m => A.Type -> m A.Type
getTypeContext def
    =  do ps <- get
          case psTypeContext ps of
            (Just c):_ -> return c
            _ -> return def

-- | Generate and define a nonce specification.
defineNonce :: PSM m => Meta -> String -> A.SpecType -> A.NameType -> A.AbbrevMode -> m A.Specification
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
          defineName n nd
          return $ A.Specification m n st

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: PSM m => Meta -> A.Process -> m A.Specification
makeNonceProc m p
    = defineNonce m "wrapper_proc" (A.Proc m [] p) A.ProcName A.Abbrev

-- | Generate and define a variable abbreviation.
makeNonceIs :: PSM m => String -> Meta -> A.Type -> A.AbbrevMode -> A.Variable -> m A.Specification
makeNonceIs s m t am v
    = defineNonce m s (A.Is m am t v) A.VariableName am

-- | Generate and define an expression abbreviation.
makeNonceIsExpr :: PSM m => String -> Meta -> A.Type -> A.Expression -> m A.Specification
makeNonceIsExpr s m t e
    = defineNonce m s (A.IsExpr m A.ValAbbrev t e) A.VariableName A.ValAbbrev

-- | Generate and define a variable.
makeNonceVariable :: PSM m => String -> Meta -> A.Type -> A.NameType -> A.AbbrevMode -> m A.Specification
makeNonceVariable s m t nt am
    = defineNonce m s (A.Declaration m t) nt am

