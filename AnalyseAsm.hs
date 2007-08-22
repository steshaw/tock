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
  , fiTotalStack = -1
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
                        AsmFunction newFunc -> (newFunc, fi)
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

-- | Stack size for unknown functions.
unknownSize :: Int
unknownSize = 512

-- | Additional stack size to give to all functions.
-- This is necessary because CCSP does odd things with the provided stack
-- size; it doesn't calculate the space that it needs for the arguments.
baseStackSize :: Int
baseStackSize = 32

-- | Add the stack sizes for called functions to their callers.
addCalls :: AAM ()
addCalls
    =  do fmap <- get
          sequence_ $ map computeStack (Map.keys fmap)
  where
    computeStack :: String -> AAM Int
    computeStack func
        =  do fmap <- get
              let fi = Map.findWithDefault emptyFI func fmap
              let tstack = fiTotalStack fi
              tstack' <- if Map.member func fmap
                           then (if tstack == -1
                                   then userFunc fi
                                   else return tstack)
                           else systemFunc func
              modify $ Map.insert func (fi { fiTotalStack = tstack' })
              return tstack'

    systemFunc :: String -> AAM Int
    systemFunc func
        =  do lift $ addPlainWarning $ "Unknown function " ++ func ++ "; allocating " ++ show unknownSize ++ " bytes stack"
              return unknownSize

    userFunc :: FunctionInfo -> AAM Int
    userFunc fi
        =  do let localStack = fiStack fi + baseStackSize
              calledStacks <- mapM computeStack $ Set.toList $ fiCalls fi
              return $ localStack + maximum (0 : calledStacks)

-- | Analyse assembler and return C source defining sizes.
analyseAsm :: String -> PassM String
analyseAsm asm
  =  do let stream = parseAsm asm
        veryDebug $ pshow stream
        info <- execStateT (collectInfo stream >> addCalls) Map.empty
        debug $ "Analysed function information:"
        debug $ concat [printf "  %-40s %5d %5d %s\n"
                          func (fiStack fi) (fiTotalStack fi)
                          (concat $ intersperse " " $ Set.toList $ fiCalls fi)
                        | (func, fi) <- Map.toList info]
        let lines = ["const int " ++ func ++ "_stack_size = " ++ show (fiTotalStack fi) ++ ";\n"
                     | (func, fi) <- Map.toList info]
        return $ concat lines
