{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

-- | Analyse the assembly output from the C compiler for stack size
-- information.

-- FIXME: This only works for x86 at the moment.
-- FIXME: This should have a "just use a huge fixed number" mode for debugging.

module AnalyseAsm (
    AsmItem(..),
    parseAsmLine, analyseAsm
  ) where

import Control.Monad.State
import Data.Char
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Numeric (readDec)
import Text.Printf

import CompState
import Errors
import Pass
import PrettyShow
import Utils

-- | Interesting things that we might find in the assembly source.
data AsmItem =
  AsmLabel String
  | AsmStackInc Int
  | AsmCall String
  deriving (Show, Eq, Data, Typeable)

-- | Examine a line of the assembly source to see whether it's something we're
-- interested in.
parseAsmLine :: String -> Maybe AsmItem
parseAsmLine s
    = case words s of
        [] -> Nothing

        -- The x86 stack goes downwards, so subl makes the stack deeper.
        ["subl", '$':arg, "%esp"] -> parseInc arg
        -- ... but GCC will sometimes generate "addl \$-n" rather than "subl
        -- \$n".
        ["addl", '$':'-':arg, "%esp"] -> parseInc arg
        -- A plain push also makes the stack deeper.
        ("pushl":_) -> Just $ AsmStackInc 4

        ["call", arg] -> parseCall arg
        -- GCC does tail-call optimisation, so we need to look for jmp as well
        -- as call.
        ["jmp", arg] -> parseCall arg

        [label] -> parseLabel label

        _ -> Nothing

  where
    -- | Parse a label: a line ending in @:@, and not starting with @.@ or a
    -- digit.
    parseLabel :: String -> Maybe AsmItem
    parseLabel s@(c:cs)
      | isDigit c || '.' `elem` s = Nothing
      | last cs == ':'            = Just $ AsmLabel (liat s)
      | otherwise                 = Nothing
      where
        liat :: String -> String
        liat = reverse . tail . reverse

    -- | Parse a stack increase: just a number.
    parseInc :: String -> Maybe AsmItem
    parseInc s
        = case readDec s of
            [(v, ",")] -> Just $ AsmStackInc v
            _ -> Nothing

    -- | Parse a called label, which mustn't start with @.@ or @*@.
    parseCall :: String -> Maybe AsmItem
    parseCall ('.':_) = Nothing
    parseCall ('*':_) = Nothing
    parseCall s = Just $ AsmCall s

-- | Turn assembly source into a list of interesting things.
parseAsm :: String -> [AsmItem]
parseAsm asm
  = catMaybes [parseAsmLine l | l <- lines asm]

data StackInfo
  = Fixed Int
  | Remote String
  | Max [StackInfo]
  | Plus StackInfo StackInfo
  deriving (Show, Data, Typeable)

findAllDependencies :: StackInfo -> Set.Set String
findAllDependencies (Remote s) = Set.singleton s
findAllDependencies (Max as) = foldl Set.union Set.empty $  map findAllDependencies as
findAllDependencies (Plus a b) = findAllDependencies a `Set.union` findAllDependencies b
findAllDependencies _ = Set.empty


-- | Information about defined functions.
data FunctionInfo = FunctionInfo {
    fiStack :: Int
  , fiTotalStack :: Maybe StackInfo
  , fiCalls :: Set.Set String
  }
  deriving (Show, Data, Typeable)

emptyFI :: FunctionInfo
emptyFI = FunctionInfo {
    fiStack = 0
  , fiTotalStack = Nothing
  , fiCalls = Set.empty
  }

-- | Monad for `AnalyseAsm` operations.
type AAM = StateT (Map.Map String FunctionInfo) PassM

instance CSMR AAM where
  getCompState = lift getCompState

-- | Collect information about each function that's been defined.
collectInfo :: [AsmItem] -> AAM ()
collectInfo ais = collectInfo' ais ""
  where
    collectInfo' :: [AsmItem] -> String -> AAM ()
    collectInfo' [] _ = return ()
    collectInfo' (ai:ais) func
        =  do fmap <- get
              let fi = Map.findWithDefault emptyFI func fmap
              let (func', fi')
                    = case ai of
                        AsmLabel newFunc -> (newFunc, fi)
                        AsmStackInc v ->
                          -- This overestimates: it adds together all the stack
                          -- allocations it finds, rather than trying to figure
                          -- out whether any of them are optional or get undone
                          -- (e.g. push; pop; push will result in allocating
                          -- two slots).
                          (func, fi {
                                   fiStack = v + fiStack fi
                                 })
                        AsmCall callFunc ->
                          (func, fi {
                                   fiCalls = Set.insert callFunc $ fiCalls fi
                                 })
              modify $ Map.insert func fi'
              collectInfo' ais func'

-- | Additional stack size to give to all functions.
-- This is necessary because CCSP does odd things with the provided stack
-- size; it doesn't calculate the space that it needs for the arguments.
baseStackSize :: Int
baseStackSize = 32

-- | Add the stack sizes for called functions to their callers.
addCalls :: [String] -> Int -> AAM ()
addCalls knownProcs unknownSize
    =  do fmap <- get
          sequence_ $ map (computeStack True) (Map.keys fmap)
  where
    computeStack :: Bool -> String -> AAM StackInfo
    computeStack processUser func
        =  do fmap <- get
              let fi = Map.findWithDefault emptyFI func fmap
              let tstack = fiTotalStack fi
              tstack' <- if Map.member func fmap && processUser
                           then (case tstack of
                                   Nothing -> userFunc fi
                                   Just x -> return x)
                           else systemFunc func
              when processUser $ modify $ Map.insert func (fi { fiTotalStack = Just tstack' })
              return tstack'

    systemFunc :: String -> AAM StackInfo
    systemFunc func
        =  do cs <- getCompState
              fmap <- get
              if func `elem` (map fst (csExternals cs) ++ knownProcs)
                then do return $ Remote $ func
                else do lift $ warnPlainP WarnInternal $ "Unknown function " ++ func
                          ++ "; allocating " ++ show unknownSize ++ " bytes stack"
                        return $ Fixed unknownSize

    userFunc :: FunctionInfo -> AAM StackInfo
    userFunc fi
        =  do let localStack = fiStack fi + baseStackSize
              calledStacks <- mapM (computeStack False) $ Set.toList $ fiCalls fi
              return $ Fixed localStack `Plus` Max (Fixed 0 : calledStacks)

-- I don't think we can use sortBy here because we only have a partial ordering,
-- not a total ordering (transitivity, for one, isn't automatic).
--
-- So our plan is as follows.  We calculate all the dependencies for each item.
-- We put all the items with no dependents first, and then we recurse, removing
-- all the no-dependent items from the dependencies of the others. 
dependenceSort :: Set.Set String -> [(String, FunctionInfo)] -> [(String, FunctionInfo)]
dependenceSort ofInterest origItems = map fst $ dependenceSort' itemsWithDependents
  where
    itemsWithDependents = [(item, ofInterest `Set.intersection`
      (maybe Set.empty findAllDependencies $ fiTotalStack $ snd item)) | item <- origItems]

    dependenceSort' :: [((String, FunctionInfo), Set.Set String)]
      -> [((String, FunctionInfo), Set.Set String)]
    dependenceSort' [] = []
    dependenceSort' items
      | null firstItems -- Infinite loop if we don't stop it:
         = error $ "Cyclic dependencies in stack sizes: "
           ++ show [n ++ " depends on " ++ show deps | ((n, _), deps) <- rest]
      | otherwise
         = firstItems ++ dependenceSort' [(item, deps `Set.difference` ignore)
                                         | (item, deps) <- rest]
      where
        (firstItems, rest) = partition (Set.null . snd) items

        ignore = Set.fromList $ map (fst . fst) firstItems
      

-- | Analyse assembler and return C source defining sizes.
analyseAsm :: Maybe [String] -> String -> PassM String
analyseAsm mprocs asm
  =  do let stream = parseAsm asm
        veryDebug $ pshow stream
        cs <- getCompState
        let unique = concat [if c `elem` (['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'])
                               then [c]
                               else '_' : show (ord c)
                            | c <- csCurrentFile cs]
        info <- execStateT (collectInfo stream >> addCalls (fromMaybe [] mprocs) (csUnknownStackSize cs)) Map.empty
        debug $ "Analysed function information:"
--        debug $ concat [printf "  %-40s %5d %5d %s\n"
--                          func (fiStack fi) (fiTotalStack fi)
--                          (concat $ intersperse " " $ Set.toList $ fiCalls fi)
--                        | (func, fi) <- Map.toList $ filterNames info]

        let lines =  -- Can't remember if max is a standard function so let's make our own:
                     "#ifndef TOCK_MAX\n#define TOCK_MAX(x,y) ((x) > (y) ? (x) : (y))\n#endif\n" :
                     ["#include \"" ++ f ++ ".tock_post.h\"\n"
                     | f <- Set.toList $ csUsedFiles cs] ++
                     ["#define " ++ func ++ "_stack_size_CPP "
                         ++ maybe "#error Unknown!" toC (fiTotalStack fi) ++ "\n"
                     ++ "const int " ++ func ++ "_stack_size = "  ++ func ++ "_stack_size_CPP;\n"
                     | (func, fi) <- dependenceSort (maybe Set.empty Set.fromList mprocs) $ Map.toList $ filterNames info]
        return $ "#ifndef INCLUDED_" ++ unique ++ "\n#define INCLUDED_" ++ unique
          ++ "\n" ++ concat lines ++ "\n#endif\n"
  where
    filterNames = case mprocs of
      Nothing -> id
      Just m -> (`Map.intersection` (Map.fromList (zip m (repeat ()))))

    findAllPlus :: StackInfo -> (Int, [StackInfo])
    findAllPlus (Fixed n) = (n, [])
    findAllPlus (Plus a b) = findAllPlus a `with` findAllPlus b
      where
        with (m, as) (n, bs) = (m + n, as ++ bs)
    findAllPlus a = (0, [a])

    -- Without  the simplifications in this function, the nesting of TOCK_MAX (and
    -- its exponentially-sized expansion) was blowing the mind of the C compiler,
    -- and the memory of my machine.
    toC :: StackInfo -> String
    toC (Fixed n) = show n
    toC (Remote s) = s ++ "_stack_size_CPP"
    toC x@(Plus {}) = let (m, as) = findAllPlus x in
      (if m == 0 then id else \x -> "(" ++ show m ++ "+" ++ x ++ ")") $
        concat (intersperse "+" $ map toC as) 
    toC (Max as) = foldl makeMax (show fixed) (map toC other)
      where
        fixed = maximum [n | Fixed n <- as]
        other = filter isNotFixed as

        makeMax a b = "TOCK_MAX(" ++ a ++ "," ++ b ++ ")"

        isNotFixed (Fixed {}) = False
        isNotFixed _ = True
