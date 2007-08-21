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

-- | Preprocess occam code.
module PreprocessOccam where

import Data.List
import qualified Data.Set as Set
import Text.Regex

import Errors
import LexOccam
import Metadata
import Pass
import StructureOccam
import Utils

import CompState
import Control.Monad.Error
import Control.Monad.State
import System
import System.IO
import PrettyShow

-- | Open an included file, looking for it in the search path.
-- Return the open filehandle and the location of the file.
-- FIXME: This doesn't actually look at the search path yet.
searchFile :: Meta -> String -> PassM (Handle, String)
searchFile m filename
    =  do cs <- get
          let currentFile = csCurrentFile cs
          let possibilities = [joinPath currentFile filename]
          openOneOf possibilities
  where
    openOneOf :: [String] -> PassM (Handle, String)
    openOneOf [] = dieP m $ "Unable to find " ++ filename
    openOneOf (fn:fns)
        =  do r <- liftIO $ maybeIO $ openFile fn ReadMode
              case r of
                Just h -> return (h, fn)
                Nothing -> openOneOf fns

-- | Preprocess a file and return its tokenised form ready for parsing.
preprocessFile :: Meta -> String -> PassM [Token]
preprocessFile m filename
    =  do (handle, realFilename) <- searchFile m filename
          liftIO $ putStrLn $ "Loading " ++ realFilename
          origCS <- get
          modify (\cs -> cs { csCurrentFile = realFilename })
          s <- liftIO $ hGetContents handle
          toks <- runLexer realFilename s >>= structureOccam >>= preprocessOccam
          modify (\cs -> cs { csCurrentFile = csCurrentFile origCS })
          return toks

-- | Preprocess a token stream.
preprocessOccam :: [Token] -> PassM [Token]
preprocessOccam [] = return []
preprocessOccam ((m, TokPreprocessor ('#':s)):(_, EndOfLine):ts)
    =  do func <- handleDirective m s
          rest <- preprocessOccam ts
          return $ func rest
-- Check the above case didn't miss something.
preprocessOccam ((_, TokPreprocessor _):_)
    = error "bad TokPreprocessor token"
preprocessOccam (t:ts)
    =  do rest <- preprocessOccam ts
          return $ t : rest

--{{{  preprocessor directive handlers
type DirectiveFunc = Meta -> [String] -> PassM ([Token] -> [Token])

-- | Call the handler for a preprocessor directive.
handleDirective :: Meta -> String -> PassM ([Token] -> [Token])
handleDirective m s = lookup s directives
  where
    -- FIXME: This should really be an error rather than a warning, but
    -- currently we support so few preprocessor directives that this is more
    -- useful.
    lookup s []
        =  do addWarning m "Unknown preprocessor directive ignored"
              return id
    lookup s ((re, func):ds)
        = case matchRegex re s of
            Just fields -> func m fields
            Nothing -> lookup s ds

-- | List of handlers for preprocessor directives.
-- `handleDirective` walks down the regexps in this list until it finds one
-- that matches, then uses the corresponding function.
directives :: [(Regex, DirectiveFunc)]
directives =
  [ (mkRegex "^INCLUDE \"(.*)\"$", handleInclude)
  , (mkRegex "^USE \"(.*)\"$", handleUse)
  ]

-- | Handle the @#INCLUDE@ directive.
handleInclude :: DirectiveFunc
handleInclude m [incName]
    =  do toks <- preprocessFile m incName
          return (\ts -> toks ++ ts)

-- | Handle the @#USE@ directive.
-- This is a bit of a hack at the moment, since it just includes the file
-- textually.
handleUse :: DirectiveFunc
handleUse m [modName]
    =  do let incName  = mangleModName modName
          cs <- get
          put $ cs { csUsedFiles = Set.insert incName (csUsedFiles cs) }
          if Set.member incName (csUsedFiles cs)
            then return id
            else handleInclude m [incName]
  where
    -- | If a module name doesn't already have a suffix, add one.
    mangleModName :: String -> String
    mangleModName mod
        = if ".occ" `isSuffixOf` mod || ".inc" `isSuffixOf` mod
            then mod
            else mod ++ ".occ"
--}}}

-- | Main function for testing.
main :: IO ()
main
    =  do (arg:_) <- getArgs
          v <- evalStateT (runErrorT (test arg)) emptyState
          case v of
            Left e -> dieIO e
            Right r -> return ()
  where
    test :: String -> PassM ()
    test fn
        = do tokens <- preprocessFile emptyMeta fn
             liftIO $ putStrLn $ pshow tokens

