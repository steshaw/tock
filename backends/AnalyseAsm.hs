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
    parseAsmLine, analyseAsm, computeFinalStackSizes
  ) where

import Control.Arrow
import Control.Monad.Error
import Control.Monad.State
import Data.Char
import Data.Generics (Data, Typeable)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Numeric (readDec)
import Text.Printf

import CompState
import Errors
import Metadata
import Pass
import PrettyShow
import Utils

-- | Interesting things that we might find in the assembly source.
data AsmItem =
  AsmLabel String
  | AsmStackInc Integer
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

data Depends
  = DependsOnSizes String
  deriving (Show, Read)

-- The stack is the fixed amount, plus the maximum of all other dependencies
data StackInfo
  = StackInfo
    { fixed :: Integer
    , occamExt :: Set.Set (Either Integer String)
    , otherExt :: Set.Set String
    }
    deriving (Data, Typeable)

instance Show StackInfo where
  show (StackInfo f occ ext)
    = "(StackInfo " ++ show f ++ " " ++ show (Set.toList occ)
        ++ " " ++ show (Set.toList ext) ++ ")"

instance Read StackInfo where
  readsPrec _
    = readParen True $ \whole -> do
        -- Let's see if I can figure out the list monad.  Each binding will bind
        -- one item from a list (of possibles), and then the subsequent part of
        -- the do will be carried out for that possibility.
        args123 <- readExact "StackInfo" whole >>* dropSpaces
        (n, args23) <- reads args123
        (occ, arg3) <- reads $ dropSpaces args23
        (ext, rest) <- reads $ dropSpaces arg3
        return (StackInfo n (Set.fromList occ) (Set.fromList ext), rest)
   where
    readExact :: String -> String -> [String]
    readExact ex str
      | ex `isPrefixOf` str = [drop (length ex) str]
      | otherwise = []

    dropSpaces :: String -> String
    dropSpaces = dropWhile isSpace

findAllOccamDependencies :: StackInfo -> Set.Set String
findAllOccamDependencies (StackInfo _ a _)
  = Set.mapMonotonic (\(Right x) -> x) $ Set.filter isRight a

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight (Left _) = False

-- | Information about defined functions.
data FunctionInfo = FunctionInfo {
    fiStack :: Integer
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
baseStackSize :: Integer
baseStackSize = 32

-- | Add the stack sizes for called functions to their callers.
addCalls :: [String] -> AAM ()
addCalls knownProcs
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
                then do return $ StackInfo
                          { fixed = 0
                          , occamExt = Set.singleton (Right func)
                          , otherExt = Set.empty
                          }
                else do lift $ warnPlainP WarnInternal $ "Unknown function " ++ func
                          ++ "; allocating arbitary stack"
                        return $ StackInfo
                          { fixed = 0
                          , occamExt = Set.empty
                          , otherExt = Set.singleton func
                          }

    userFunc :: FunctionInfo -> AAM StackInfo
    userFunc fi
        =  do let localStack = fiStack fi + baseStackSize
              calledStacks <- mapM (computeStack False) $ Set.toList $ fiCalls fi
              return $ foldl mergeStackInfo (StackInfo localStack Set.empty Set.empty) calledStacks
     where
       mergeStackInfo (StackInfo n as bs) (StackInfo n' as' bs')
         = StackInfo (n + n') (as `Set.union` as') (bs `Set.union` bs')

substituteFull :: Integer -> [(String, StackInfo)] -> Either String [(String, Integer)]
substituteFull unknownSize origItems
  = case foldl Set.union Set.empty (map (findAllOccamDependencies . snd) origItems)
           `Set.difference` Set.fromList (map fst origItems) of
      s | Set.null s -> case map fst origItems \\ nub (map fst origItems) of
           [] -> substitute' [] origItems
           dups -> throwError $ "Duplicate stack sizes for: " ++ show dups
        | otherwise -> throwError $ "Missing stack sizes for: " ++ show s
  where
    substitute' :: [(String, Integer)] -> [(String, StackInfo)] -> Either String [(String, Integer)]
    substitute' acc [] = return acc
    substitute' acc items
      | null firstItems -- Infinite loop if we don't stop it:
         = throwError $ "Cyclic dependencies in stack sizes: "
           ++ unlines [n ++ " depends on " ++ show (occamExt s) | (n, s) <- rest]
           ++ " done processes are: " ++ show (map fst origItems \\ map fst rest)
      | otherwise
         = substitute' (acc++newAcc)
             [(item, s { occamExt = Set.map subAll $ occamExt s })
             | (item, s) <- rest]
      where
        (firstItems, rest) = partition (Set.null . Set.filter isRight . occamExt
          . snd) items

        newAcc = map (second getFixed) firstItems

        -- We know occamExt must be all Lefts:
        getFixed (StackInfo {fixed = fix, occamExt = occ, otherExt = ext})
          = fix + maximum ((if Set.null ext then 0 else unknownSize)
                           : [n | Left n <- Set.toList occ])

        subAll (Left n) = Left n
        subAll (Right n) = case lookup n newAcc of
                             Nothing -> Right n
                             Just s -> Left s

substitutePartial :: [(String, StackInfo)] -> [(String, StackInfo)]
substitutePartial origItems = substitute' [] origItems
  where
    substitute' :: [(String, StackInfo)] -> [(String, StackInfo)] -> [(String, StackInfo)]
    substitute' acc [] = acc
    substitute' acc items
      | null firstItems -- Infinite loop if we don't stop it:
         = acc ++ items -- Got as far as we can
      | otherwise
         = substitute' (acc++newAcc)
             [(item, Set.fold subAll (s {occamExt = Set.empty}) (occamExt s))
             | (item, s) <- rest]
      where
        (firstItems, rest) = partition (Set.null . Set.filter isRight . occamExt
          . snd) items

        newAcc = map (second getFixed) firstItems

        -- We know occamExt must be all Lefts:
        getFixed (StackInfo {fixed = fix, occamExt = occ, otherExt = ext})
          = StackInfo {fixed = fix + (maximum $ 0 : [n | Left n <- Set.toList occ])
                      ,occamExt = Set.empty
                      ,otherExt = ext
                      }

        subAll :: Either Integer String -> StackInfo -> StackInfo
        subAll (Left n) s = s { fixed = fixed s + n}
        subAll (Right n) s
          = case lookup n newAcc of
              Nothing -> s { occamExt = Set.insert (Right n) (occamExt s) }
              Just ds -> ds { fixed = fixed s + fixed ds
                            , otherExt = Set.union (otherExt s) (otherExt ds) }
      

-- | Analyse assembler and return C source defining sizes.
--
-- The first parameter is a possible list of occam PROCs, so we know which stuff
-- to mark as occam and which to mark as unknown external.
--
-- The return value is a string to be written to a file, that can later be read
-- in and understood by computeFinalStackSizes
analyseAsm :: Maybe [String] -> [String] -> String -> PassM String
analyseAsm mprocs deps asm
  =  do let stream = parseAsm asm
        veryDebug $ pshow stream
        cs <- getCompState
        info <- execStateT (collectInfo stream >> addCalls (fromMaybe [] mprocs)) Map.empty
        debug $ "Analysed function information:"
        debug $ concat [printf "  %-40s %5d %s %s\n"
                          func (fiStack fi) (show $ fiTotalStack fi)
                          (concat $ intersperse " " $ Set.toList $ fiCalls fi)
                        | (func, fi) <- Map.toList info]
        let info' = Map.fromList $ substitutePartial
                      [(s, st) | (s, (FunctionInfo {fiTotalStack=Just st}))
                                   <- Map.toList info]
        return $ unlines $ map (show . DependsOnSizes) deps ++
                    map show (Map.toList $ filterNames info')
  where
    filterNames = case mprocs of
      Nothing -> id
      Just m -> (`Map.intersection` (Map.fromList (zip m (repeat ()))))

-- The String is the contents of the stack sizes file for the last one in the chain,
-- straight from analyseAsm.  The function is used to read in files when needed,
-- by looking in the search path.  The Int is the unknown-stack-size.
--
-- The output is the contents of a C file with all the stack sizes.
computeFinalStackSizes :: forall m. (Monad m, Die m) => (Meta -> String -> m String) -> Integer -> Meta
  -> String -> m String
computeFinalStackSizes readSizesFor unknownSize m beginSizes
  = do infos <- evalStateT (readInAll m beginSizes) Set.empty
       let finalised = substituteFull unknownSize infos
       case finalised of
         Left err -> dieP emptyMeta err
         Right x -> return $ toC x
  where
    readInAll :: Meta -> String -> StateT (Set.Set String) m [(String, StackInfo)]
    readInAll curFile contents
      = do (deps, info) <- lift $ split curFile (zip [1..] $ lines contents)
           concatMapM (\(askedMeta, newFile) -> readSizesFor' askedMeta newFile
                          >>= readInAll (Meta (Just newFile) 1 1))
             deps >>* (++ info)

    readSizesFor' :: Meta -> String ->  StateT (Set.Set String) m String
    readSizesFor' m fn = do prevFiles <- get
                            if Set.member fn prevFiles
                              then return ""
                              else do modify (Set.insert fn)
                                      lift $ readSizesFor m fn

    split :: Meta -> [(Int, String)] -> m ([(Meta, String)], [(String, StackInfo)])
    split _ [] = return ([], [])
    split m ((n,l):ls) = case (reads l, reads l) of
      ([(DependsOnSizes dep, rest)], []) | all isSpace rest ->
        liftM (transformPair ((m { metaLine = n}, dep):) id) $ split m ls
      ([], [(s, rest)]) | all isSpace rest -> liftM (transformPair id (s:)) $ split m ls
      _ -> dieP (m {metaLine = n}) $ "Cannot parse line: " ++ l

    toC :: [(String, Integer)] -> String
    toC info = unlines [ "const int " ++ nm ++ "_stack_size = " ++ show s ++ ";\n"
                       | (nm, s) <- info]
