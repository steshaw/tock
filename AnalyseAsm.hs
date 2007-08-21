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

-- | Analyse the assembly output from the C compiler for stack size
-- information.

-- FIXME: This only works for x86 at the moment.
-- FIXME: This should have a "just use a huge fixed number" mode for debugging.

module AnalyseAsm (analyseAsm) where

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Numeric (readDec)
import System
import Text.Printf
import Text.Regex

import CompState
import Errors
import Pass
import PrettyShow

-- | Interesting things that we might find in the assembly source.
data AsmItem =
  AsmFunction String
  | AsmStackInc Int
  | AsmCall String
  deriving (Show, Eq, Data, Typeable)

-- | Examine a line of the assembly source to see whether it's something we're
-- interested in.
parseAsmLine :: String -> Maybe AsmItem
parseAsmLine s
    = matchLabel s' `mplus` matchInc s' `mplus` matchPush s' `mplus` matchCall s'
  where
    s' = trim s

    trim :: String -> String
    trim s = subRegex wsRE (subRegex startwsRE (subRegex endwsRE s "") "") " "
      where
        wsRE = mkRegex "[[:space:]]+"
        startwsRE = mkRegex "^[[:space:]]+"
        endwsRE = mkRegex "[[:space:]]+$"

    matchLabel :: String -> Maybe AsmItem
    matchLabel s
        = case matchRegex labelRE s of
            Just [l] -> Just $ AsmFunction l
            _ -> Nothing
      where
        labelRE = mkRegex "^([^\\.0-9][a-zA-Z0-9_]*):$"

    matchInc :: String -> Maybe AsmItem
    matchInc s
        = case matchRegex incdecRE s of
            Just [v] -> Just $ AsmStackInc (parseVal v)
            _ -> Nothing
      where
        -- The x86 stack goes downwards, so subl makes the stack deeper.
        incdecRE = mkRegex "^subl (.*), %esp$"

        parseVal :: String -> Int
        parseVal ('$':s)
            = case readDec s of
                [(v, "")] -> v
                _ -> error $ "Don't know how to parse assembly literal: " ++ s
        parseVal s = error $ "Really don't know how to parse assembly literal: " ++ s

    matchPush :: String -> Maybe AsmItem
    matchPush s
        = case matchRegex pushRE s of
            Just [] -> Just $ AsmStackInc 4
            _ -> Nothing
      where
        pushRE = mkRegex "^pushl"

    matchCall :: String -> Maybe AsmItem
    matchCall s
        = case matchRegex callRE s of
            Just [_, l] -> Just $ AsmCall l
            _ -> Nothing
      where
        -- GCC does tail-call optimisation, so we need to look for jmp as well
        -- as call.
        callRE = mkRegex "^(jmp|call) ([^\\.\\*].*)$"

-- | Turn assembly source into a list of interesting things.
parseAsm :: String -> [AsmItem]
parseAsm asm
  = catMaybes [parseAsmLine l | l <- lines asm]

-- | Information about defined functions.
data FunctionInfo = FunctionInfo {
    fiStack :: Int
  , fiTotalStack :: Int
  , fiCalls :: Set.Set String
  }
  deriving (Show, Data, Typeable)

emptyFI :: FunctionInfo
emptyFI = FunctionInfo {
    fiStack = 0
  , fiTotalStack = 0
  , fiCalls = Set.empty
  }

type FuncMap = Map.Map String FunctionInfo

-- | Collect information about each function that's been defined.
collectInfo :: [AsmItem] -> FuncMap
collectInfo ais = collectInfo' ais "" Map.empty
  where
    collectInfo' :: [AsmItem] -> String -> FuncMap -> FuncMap
    collectInfo' [] _ fmap = fmap
    collectInfo' (ai:ais) func fmap
        = case ai of
            AsmFunction newFunc ->
              let fi = Map.findWithDefault emptyFI func fmap
                in collectInfo' ais newFunc (Map.insert func fi fmap)
            AsmStackInc v ->
              let ofi = Map.findWithDefault emptyFI func fmap
                  -- This overestimates: it adds together all the stack
                  -- allocations it finds, rather than trying to figure out
                  -- whether any of them are optional or get undone (e.g. push;
                  -- pop; push will result in allocating two slots).
                  fi = ofi { fiStack = v + fiStack ofi }
                in collectInfo' ais func (Map.insert func fi fmap)
            AsmCall callFunc ->
              let ofi = Map.findWithDefault emptyFI func fmap
                  fi = ofi { fiCalls = Set.insert callFunc $ fiCalls ofi  }
                in collectInfo' ais func (Map.insert func fi fmap)

-- | Stack size for unknown functions.
unknownSize :: Int
unknownSize = 512

-- | Additional stack size to give to all functions.
baseStackSize :: Int
baseStackSize = 16

-- | Add the stack sizes for called functions to their callers.
addCalls :: FuncMap -> PassM FuncMap
addCalls fmap
    =  do l <- mapM addCalls' (Map.toList fmap)
          return $ Map.fromList l
  where
    addCalls' :: (String, FunctionInfo) -> PassM (String, FunctionInfo)
    addCalls' (func, fi)
        =  do stack <- totalStack func
              return (func, fi { fiTotalStack = stack })

    totalStack :: String -> PassM Int
    totalStack func
        = if Map.member func fmap
            then knownStack func
            -- FIXME: We should have a list of known system functions.
            else do addPlainWarning $ "Unknown function " ++ func ++ "; allocating " ++ show unknownSize ++ " bytes stack"
                    return unknownSize

    knownStack :: String -> PassM Int
    knownStack func
        =  do let fi = fmap Map.! func
              let localStack = fiStack fi + baseStackSize
              calledStacks <- mapM totalStack $ Set.toList $ fiCalls fi
              return $ localStack + maximum (0 : calledStacks)

-- | Analyse assembler and return C source defining sizes.
analyseAsm :: String -> PassM String
analyseAsm asm
  =  do let stream = parseAsm asm
        veryDebug $ pshow stream
        info <- addCalls $ collectInfo stream
        debug $ "Analysed function information:"
        debug $ concat [printf "  %-40s %5d %5d %s\n"
                          func (fiStack fi) (fiTotalStack fi)
                          (concat $ intersperse " " $ Set.toList $ fiCalls fi)
                        | (func, fi) <- Map.toList info]
        let lines = ["const int " ++ func ++ "_stack_size = " ++ show (fiTotalStack fi) ++ ";\n"
                     | (func, fi) <- Map.toList info]
        return $ concat lines

