-- | Compiler state.
module ParseState where

import Data.Generics
import Data.Map (Map)
import qualified Data.Map as Map
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
    psSourceFiles :: Map String String,
    psIndentLinesIn :: [String],
    psIndentLinesOut :: [String],

    -- Set by Parse
    psLocalNames :: [(String, A.Name)],
    psMainLocals :: [(String, A.Name)],
    psNames :: Map String A.NameDef,
    psNameCounter :: Int,
    psTypeContext :: [Maybe A.Type],
    psLoadedFiles :: [String],
    psWarnings :: [String],

    -- Set by passes
    psNonceCounter :: Int,
    psFunctionReturns :: Map String [A.Type],
    psPulledItems :: [[A.Structured -> A.Structured]],
    psAdditionalArgs :: Map String [A.Actual]
  }
  deriving (Show, Data, Typeable)

instance Show (A.Structured -> A.Structured) where
  show p = "(function on Structured)"

emptyState :: ParseState
emptyState = ParseState {
    psVerboseLevel = 0,
    psParseOnly = False,
    psOutputFile = "-",

    psSourceFiles = Map.empty,
    psIndentLinesIn = [],
    psIndentLinesOut = [],

    psLocalNames = [],
    psMainLocals = [],
    psNames = Map.empty,
    psNameCounter = 0,
    psTypeContext = [],
    psLoadedFiles = [],
    psWarnings = [],

    psNonceCounter = 0,
    psFunctionReturns = Map.empty,
    psPulledItems = [],
    psAdditionalArgs = Map.empty
  }

-- | Class of monads which keep a ParseState.
-- (This is just shorthand for the equivalent MonadState constraint.)
class MonadState ParseState m => PSM m
instance MonadState ParseState m => PSM m

--{{{  name definitions
-- | Add the definition of a name.
defineName :: PSM m => A.Name -> A.NameDef -> m ()
defineName n nd
    = modify $ (\ps -> ps { psNames = Map.insert (A.nameName n) nd (psNames ps) })

-- | Find the definition of a name.
lookupName :: (PSM m, Die m) => A.Name -> m A.NameDef
lookupName n
    =  do ps <- get
          case Map.lookup (A.nameName n) (psNames ps) of
            Just nd -> return nd
            Nothing -> die $ "cannot find name " ++ A.nameName n
--}}}

--{{{  warnings
-- | Add a warning.
addWarning :: PSM m => Meta -> String -> m ()
addWarning m s = modify (\ps -> ps { psWarnings = msg : psWarnings ps })
  where msg = "Warning: " ++ show m ++ ": " ++ s
--}}}

--{{{  pulled items
-- | Enter a pulled-items context.
pushPullContext :: PSM m => m ()
pushPullContext = modify (\ps -> ps { psPulledItems = [] : psPulledItems ps })

-- | Leave a pulled-items context.
popPullContext :: PSM m => m ()
popPullContext = modify (\ps -> ps { psPulledItems = tail $ psPulledItems ps })

-- | Add a pulled item to the collection.
addPulled :: PSM m => (A.Structured -> A.Structured) -> m ()
addPulled item
    = modify (\ps -> case psPulledItems ps of
                       (l:ls) -> ps { psPulledItems = (item:l):ls })

-- | Do we currently have any pulled items?
havePulled :: PSM m => m Bool
havePulled
    =  do ps <- get
          case psPulledItems ps of
            ([]:_) -> return False
            _ -> return True

-- | Apply pulled items to a Structured.
applyPulled :: PSM m => A.Structured -> m A.Structured
applyPulled ast
    =  do ps <- get
          case psPulledItems ps of
            (l:ls) -> do put $ ps { psPulledItems = [] : ls }
                         return $ foldl (\p f -> f p) ast l
--}}}

--{{{  type contexts
-- | Enter a type context.
pushTypeContext :: PSM m => Maybe A.Type -> m ()
pushTypeContext t
    = modify (\ps -> ps { psTypeContext = t : psTypeContext ps })

-- | Leave a type context.
popTypeContext :: PSM m => m ()
popTypeContext
    = modify (\ps -> ps { psTypeContext = tail $ psTypeContext ps })

-- | Get the current type context, if there is one.
getTypeContext :: PSM m => m (Maybe A.Type)
getTypeContext
    =  do ps <- get
          case psTypeContext ps of
            (Just c):_ -> return $ Just c
            _ -> return Nothing
--}}}

--{{{ nonces
-- | Generate a throwaway unique name.
makeNonce :: PSM m => String -> m String
makeNonce s
    =  do ps <- get
          let i = psNonceCounter ps
          put ps { psNonceCounter = i + 1 }
          return $ s ++ "_n" ++ show i

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
                     A.ndAbbrevMode = am,
                     A.ndPlacement = A.Unplaced
                   }
          defineName n nd
          return $ A.Specification m n st

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: PSM m => Meta -> A.Process -> m A.Specification
makeNonceProc m p
    = defineNonce m "wrapper_proc" (A.Proc m A.PlainSpec [] p) A.ProcName A.Abbrev

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
--}}}
