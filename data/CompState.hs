{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- | Compiler state.
module CompState where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import qualified AST as A
import Errors (Die, dieP, ErrorReport, Warn, WarningType(..), warnP, WarningReport)
import Metadata
import OrdAST ()
import TypeSizes
import UnifyType
import Utils

-- | Modes that Tock can run in.
data CompMode = ModeFlowGraph | ModeLex | ModeHTML | ModeParse | ModeCompile | ModePostC | ModeFull
  deriving (Show, Data, Typeable, Eq)

-- | Backends that Tock can use.
data CompBackend = BackendC | BackendCPPCSP | BackendDumpAST | BackendSource
  deriving (Show, Data, Typeable, Eq)

-- | Frontends that Tock can use.
data CompFrontend = FrontendOccam | FrontendRain
  deriving (Show, Data, Typeable, Eq)

-- | Preprocessor definitions.
data PreprocDef =
  PreprocNothing
  | PreprocInt String
  | PreprocString String
  deriving (Show, Data, Typeable, Eq)

-- | The general type of a name.
-- This is used by the parser to indicate what sort of name it's expecting in a
-- particular context; in later passes you can look at how the name is actually
-- defined, which is more useful.
data NameType =
  ChannelName | ChanBundleName | DataTypeName | FunctionName | FieldName | PortName
  | ProcName | ProtocolName | RecordName | TagName | TimerName | VariableName
  deriving (Show, Eq, Typeable, Data)

-- | An item that has been pulled up.
type PulledItem = (Meta, Either A.Specification A.Process) -- Either Spec or ProcThen

-- | An index to identify an item involved in the type unification.
newtype UnifyIndex = UnifyIndex (Meta, Either Int A.Name)
  deriving (Typeable, Data)

instance Show UnifyIndex where
  show (UnifyIndex (m,u)) = show m ++ ": " ++ either (const "<anon>") show u

instance Eq UnifyIndex where
  (UnifyIndex (_,u)) == (UnifyIndex (_,u')) = u == u'

instance Ord UnifyIndex where
  compare (UnifyIndex (_,u)) (UnifyIndex (_,u'))
    = compare u u'

-- | An entry in the map corresponding to a UnifyIndex
type UnifyValue = TypeExp A.Type

data NameAttr = NameShared | NameAliasesPermitted deriving (Typeable, Data, Eq, Show, Ord)

data ExternalType = ExternalOldStyle | ExternalOccam
  deriving (Typeable, Data, Eq, Show, Ord)

-- | State necessary for compilation.
data CompState = CompState {
    -- This structure needs to be printable with pshow.
    -- There are explicit rules for the Maps and Sets used here
    -- in PrettyShow.hs; if you add any new ones here then remember
    -- to add matching rules there.

    -- Set by Main (from command-line options)
    csMode :: CompMode,
    csBackend :: CompBackend,
    csFrontend :: CompFrontend,
    csHasMain :: Bool,
    csCompilerFlags :: String,
    csCompilerLinkFlags :: String,
    csSanityCheck :: Bool,
    csUsageChecking :: Bool,
    csVerboseLevel :: Int,
    csOutputFile :: String,
    csOutputHeaderFile :: String,
    csOutputIncFile :: Maybe String,
    csKeepTemporaries :: Bool,
    csEnabledWarnings :: Set WarningType,
    csRunIndent :: Bool,
    csClassicOccamMobility :: Bool,
    csUnknownStackSize :: Int,
    csSearchPath :: [String],

    -- Set by preprocessor
    csCurrentFile :: String, -- Also used by some later passes!
    csUsedFiles :: Set String,
    csDefinitions :: Map String PreprocDef,

    -- Set by Parse
    csLocalNames :: [(String, (A.Name, NameType))],
    csMainLocals :: [(String, (A.Name, NameType))],
    csNames :: Map String A.NameDef,
    csUnscopedNames :: Map String String,
    csNameCounter :: Int,
    csNameAttr :: Map String (Set.Set NameAttr),
    -- A list of all the things that were at the top-level before we pull anything
    -- up (and therefore the things that should be visible to other files during
    -- separate compilation)
    csOriginalTopLevelProcs :: [String],
    csExternals :: [(String, (ExternalType, [A.Formal]))],
    -- Maps an array variable name to the name of its _sizes array:
    csArraySizes :: Map String A.Name,
    -- Stores a map of constant sizes arrays declared for that size:
    csGlobalSizes :: Map [Int] String,

    -- Set by passes
    csTypeContext :: [Maybe A.Type],
    csNonceCounter :: Int,
    csFunctionReturns :: Map String [A.Type],
    csPulledItems :: [[PulledItem]],
    csAdditionalArgs :: Map String [A.Actual],
    csParProcs :: Set A.Name,
    csUnifyId :: Int,
    csWarnings :: [WarningReport]
  }
  deriving (Data, Typeable, Show)

emptyState :: CompState
emptyState = CompState {
    csMode = ModeFull,
    csBackend = BackendC,
    csFrontend = FrontendOccam,
    csHasMain = True,
    csCompilerFlags = "",
    csCompilerLinkFlags = "",
    csSanityCheck = False,
    csUsageChecking = True,
    csVerboseLevel = 0,
    csOutputFile = "-",
    csOutputHeaderFile = "-",
    csOutputIncFile = Nothing,
    csKeepTemporaries = False,
    csEnabledWarnings = Set.fromList
      [ WarnInternal
      , WarnParserOddity
      , WarnUnknownPreprocessorDirective
      , WarnUnusedVariable],
-- TODO enable WarnUninitialisedVariable by default
    csRunIndent = False,
    csClassicOccamMobility = False,
    csUnknownStackSize = 512,
    csSearchPath = ["."],

    csCurrentFile = "none",
    csUsedFiles = Set.empty,
    csDefinitions = Map.fromList [("COMPILER.TOCK", PreprocNothing)
                                 ,("TARGET.BITS.PER.WORD", PreprocInt $ show $ cIntSize * 8)
                                 ,("TARGET.BYTES.PER.WORD", PreprocInt $ show cIntSize)
--                                 ,("TARGET.HAS.FPU", PreprocNothing)
                                 ],

    csLocalNames = [],
    csMainLocals = [],
    csNames = Map.empty,
    csUnscopedNames = Map.empty,
    csNameCounter = 0,
    csNameAttr = Map.empty,
    csOriginalTopLevelProcs = [],
    csExternals = [],
    csArraySizes = Map.empty,
    csGlobalSizes = Map.empty,

    csTypeContext = [],
    csNonceCounter = 0,
    csFunctionReturns = Map.empty,
    csPulledItems = [],
    csAdditionalArgs = Map.empty,
    csParProcs = Set.empty,
    csUnifyId = 0,
    csWarnings = []
  }

-- | Class of monads which keep a CompState.
-- (This is just shorthand for the equivalent MonadState constraint.)
class (CSMR m, MonadState CompState m) => CSM m
instance (CSMR m, MonadState CompState m) => CSM m

-- | This class is like a specific instance of MonadReader.  I tried playing
-- with introducing all sorts of MonadReader classes, trying to infer it from
-- MonadState.  But due to various problems (you can't directly infer MonadReader
-- from MonadState, you can't easily stack different MonadReader instances, etc)
-- this was the easiest method to get a read-only CompState monad.
--
-- If you introduce new monads or monad transformers elsewhere in the code you
-- may have to define your own instance (see for example, ParseOccam or GenerateCBased)
class Monad m => CSMR m where
  getCompState :: m CompState

instance Monad m => CSMR (ReaderT CompState m) where
  getCompState = ask

instance Monad m => CSMR (StateT CompState m) where
  getCompState = get

instance CSMR (Reader CompState) where
  getCompState = ask

instance CSMR (State CompState) where
  getCompState = get

instance (CSMR m, Error e) => CSMR (ErrorT e m) where
  getCompState = lift getCompState

instance (CSMR m, Monoid w) => CSMR (WriterT w m) where
  getCompState = lift getCompState


--instance (MonadWriter [WarningReport] m) => Warn m where
--  warnReport r = tell [r]

--{{{  name definitions
-- | Add the definition of a name.
defineName :: CSM m => A.Name -> A.NameDef -> m ()
defineName n nd
    = modify $ (\ps -> ps { csNames = Map.insert (A.nameName n) nd (csNames ps) })

-- | Modify the definition of a name.
modifyName :: CSM m => A.Name -> (A.NameDef -> A.NameDef) -> m ()
modifyName n f
    = modify $ (\ps -> ps { csNames = modifyName $ csNames ps })
  where
    modifyName = Map.adjust f (A.nameName n)

-- | Find the definition of a name.
lookupName :: (CSMR m, Die m) => A.Name -> m A.NameDef
lookupName n = lookupNameOrError n (dieP (findMeta n) $ "cannot find name " ++ A.nameName n)

nameSource :: (CSMR m, Die m) => A.Name -> m A.NameSource
nameSource n = lookupName n >>* A.ndNameSource

-- | Make a name unique by appending a suffix to it.
makeUniqueName :: CSM m => Meta -> String -> m String
makeUniqueName m s
    = do cs <- getCompState
         munged <- if maybe "" (++ ".tock.inc") (metaFile m)
                        `Set.member` csUsedFiles cs
                     -- For #USEd files, keep the filename stable:
                     then return $ mungeMeta m
                     -- For #INCLUDEd files, they might be included twice, so we
                     -- still need the extra suffixes:
                     else do put $ cs { csNameCounter = csNameCounter cs + 1 }
                             return $ "u" ++ show (csNameCounter cs)
         return $ s ++ "_" ++ munged

mungeMeta :: Meta -> String
mungeMeta m  = [if c `elem` (['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'])
                  then c
                  else '_'
               | c <- show m]

-- | Find an unscoped name -- or define a new one if it doesn't already exist.
findUnscopedName :: CSM m => A.Name -> m A.Name
findUnscopedName n@(A.Name m s)
    =  do st <- get
          case Map.lookup s (csUnscopedNames st) of
            Just s' -> return $ A.Name m s'
            Nothing ->
              do s' <- makeUniqueName m s
                 modify (\st -> st { csUnscopedNames = Map.insert s s' (csUnscopedNames st) })
                 let n = A.Name m s'
                 let nd = A.NameDef { A.ndMeta = m
                                    , A.ndName = s'
                                    , A.ndOrigName = s
                                    , A.ndSpecType = A.Unscoped m
                                    , A.ndAbbrevMode = A.Original
                                    , A.ndNameSource = A.NameUser
                                    , A.ndPlacement = A.Unplaced
                                    }
                 defineName n nd
                 return n

--}}}

--{{{  pulled items
-- | Enter a pulled-items context.
pushPullContext :: CSM m => m ()
pushPullContext = modify (\ps -> ps { csPulledItems = [] : csPulledItems ps })

-- | Leave a pulled-items context.
popPullContext :: CSM m => m ()
popPullContext = modify (\ps -> ps { csPulledItems = tail $ csPulledItems ps })

-- | Add a pulled item to the collection.
addPulled :: CSM m => PulledItem -> m ()
addPulled item
    = modify (\ps -> case csPulledItems ps of
                       (l:ls) -> ps { csPulledItems = (item:l):ls })

-- | Do we currently have any pulled items?
havePulled :: CSMR m => m Bool
havePulled
    =  do ps <- getCompState
          case csPulledItems ps of
            ([]:_) -> return False
            _ -> return True

-- | Apply pulled items to a Structured.
applyPulled :: (CSM m, Data a) => A.Structured a -> m (A.Structured a)
applyPulled ast
    =  do ps <- get
          case csPulledItems ps of
            (l:ls) -> do put $ ps { csPulledItems = [] : ls }
                         return $ foldl (\p f -> apply f p) ast l
  where
    apply :: Data a => PulledItem -> A.Structured a -> A.Structured a
    apply (m, Left spec) = A.Spec m spec
    apply (m, Right proc) = A.ProcThen m proc

--}}}

--{{{  type contexts
-- | Enter a type context.
pushTypeContext :: CSM m => Maybe A.Type -> m ()
pushTypeContext t
    = modify (\ps -> ps { csTypeContext = t : csTypeContext ps })

-- | Leave a type context.
popTypeContext :: CSM m => m ()
popTypeContext
    = modify (\ps -> ps { csTypeContext = tail $ csTypeContext ps })

-- | Get the current type context, if there is one.
getTypeContext :: CSMR m => m (Maybe A.Type)
getTypeContext
    =  do ps <- getCompState
          case csTypeContext ps of
            (Just c):_ -> return $ Just c
            _ -> return Nothing
--}}}

--{{{ nonces
-- | Generate a throwaway unique name.
makeNonce :: CSM m => Meta -> String -> m String
makeNonce m s
    =  do ps <- get
          let i = csNonceCounter ps
          put ps { csNonceCounter = i + 1 }
          return $ s ++ mungeMeta m ++ "_n" ++ show i

-- | Generate and define a nonce specification.
defineNonce :: CSM m => Meta -> String -> A.SpecType -> A.AbbrevMode -> m A.Specification
defineNonce m s st am
    =  do ns <- makeNonce m s
          let n = A.Name m ns
          let nd = A.NameDef {
                     A.ndMeta = m,
                     A.ndName = ns,
                     A.ndOrigName = ns,
                     A.ndSpecType = st,
                     A.ndAbbrevMode = am,
                     A.ndNameSource = A.NameNonce,
                     A.ndPlacement = A.Unplaced
                   }
          defineName n nd
          return $ A.Specification m n st


-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: CSM m => Meta -> A.Process -> m A.Specification
makeNonceProc m p
    = defineNonce m "wrapper_proc" (A.Proc m (A.PlainSpec, A.PlainRec) [] p) A.Abbrev

-- | Generate and define a counter for a replicator.
makeNonceCounter :: CSM m => String -> Meta -> m A.Name
makeNonceCounter s m
    =  do (A.Specification _ n _) <- defineNonce m s (A.Declaration m A.Int) A.ValAbbrev
          return n

-- | Generate and define a variable abbreviation.
makeNonceIs :: CSM m => String -> Meta -> A.Type -> A.AbbrevMode -> A.Variable -> m A.Specification
makeNonceIs s m t am v
    = defineNonce m s (A.Is m am t (A.ActualVariable v)) am

-- | Generate and define an expression abbreviation.
makeNonceIsExpr :: CSM m => String -> Meta -> A.Type -> A.Expression -> m A.Specification
makeNonceIsExpr s m t e
    = defineNonce m s (A.Is m A.ValAbbrev t (A.ActualExpression e)) A.ValAbbrev

-- | Generate and define a variable.
makeNonceVariable :: CSM m => String -> Meta -> A.Type -> A.AbbrevMode -> m A.Specification
makeNonceVariable s m t am
    = defineNonce m s (A.Declaration m t) am
--}}}

diePC :: (CSMR m, Die m) => Meta -> m String -> m a
diePC m str = str >>= (dieP m)

warnPC :: (CSMR m, Warn m) => Meta -> WarningType -> m String -> m ()
warnPC m t str = str >>= (warnP m t)

--dieC :: (CSM m, Die m) => m String -> m a
--dieC str = str >>= die

throwErrorC :: (CSMR m,MonadError ErrorReport m) => (Maybe Meta,m String) -> m a
throwErrorC (m,str) = str >>= ((curry throwError) m)

findAllProcesses :: CSMR m => m [(String,A.Process)]
findAllProcesses
  = do st <- getCompState
       return $ mapMaybe findAllProcesses' (Map.assocs $ csNames st)
  where
    findAllProcesses' :: (String, A.NameDef) -> Maybe (String, A.Process)
    findAllProcesses' (n, nd)
      = case A.ndSpecType nd of
          A.Proc _ _ _ p -> Just (n, p)
          _ -> Nothing

-- | A new identifer for the unify types in the tree
getUniqueIdentifer :: CSM m => m Int
getUniqueIdentifer = do st <- get
                        let n = csUnifyId st
                        put st {csUnifyId = n + 1}
                        return n

lookupNameOrError :: CSMR m => A.Name -> m A.NameDef -> m A.NameDef
lookupNameOrError n err
    =  do ps <- getCompState
          case Map.lookup (A.nameName n) (csNames ps) of
            Just nd -> return nd
            Nothing -> err

-- | Gets the 'A.SpecType' for a given 'A.Name' from the recorded types in the 'CompState'.  Dies with an error if the name is unknown.
specTypeOfName :: (CSMR m, Die m) => A.Name -> m A.SpecType
specTypeOfName n
    = liftM A.ndSpecType (lookupNameOrError n $ dieP (A.nameMeta n) $ "Could not find type in specTypeOfName for: " ++ (show $ A.nameName n))

