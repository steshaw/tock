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

-- | Error handling and reporting.
module Errors (addPlainWarning, addWarning, checkJust, Die(..), dieInternal, dieIO, dieP, ErrorReport, showWarnings, Warn(..), WarningReport) where

import Control.Monad.Error
import Control.Monad.Trans
import Data.List
import System.IO
import System.IO.Error

import Metadata

type ErrorReport = (Maybe Meta, String)

instance Error ErrorReport where
  strMsg s = (Nothing, s)

-- | Class of monads that can fail.
class Monad m => Die m where
  dieReport :: ErrorReport -> m a

-- | Fail, giving a position and an error message.
dieP :: Die m => Meta -> String -> m a
dieP m s = dieReport (Just m,s)

type WarningReport = (Maybe Meta, String)

class Monad m => Warn m where
  warnReport :: WarningReport -> m ()

--{{{  warnings
-- | Add a warning with no source position.
addPlainWarning :: Warn m => String -> m ()
addPlainWarning msg = warnReport (Nothing, msg)

-- | Add a warning.
addWarning :: Warn m => Meta -> String -> m ()
addWarning m s = warnReport (Just m, s)
--}}}

-- | Wrapper around error that gives nicer formatting, and prints out context
--
dieIO :: (Monad m, MonadIO m) => ErrorReport -> m a
dieIO (Just m@(Meta (Just fn) line column),s) = liftIO $
       -- If we can't read the file successfully, still print our original error
       -- rather than a "can't read file" error:
    do fileContents <- catch (readFile fn) (\_ -> printError (show m ++ s))
       let startingLine = max 1 (line - contextLines)
       let lines = map replaceTabs $ getLines fileContents (startingLine) ((2 * contextLines) + 1)
       putStrLn $ fn ++ ":"
       printLines startingLine (take (line - startingLine + 1) lines)
       putStr "Here"
       replicateM_ column (putChar '-')   -- column is unit-based, but we want an extra dash anyway
       putStrLn "^"
       printLines (line + 1) (drop (line - startingLine + 1) lines)
       putStrLn ""
       printError $ (show m) ++ " " ++ s
         where
           contextLines :: Int
           contextLines = 5
           -- start is unit-based, so we need to convert to zero-based
           getLines :: String -> Int -> Int -> [String]
           getLines all start total = take total (drop (start - 1) (lines all))
           printLines :: Int -> [String] -> IO ()
           printLines n lines = mapM_ (\(n,s) -> (putStrLn . ((++) (justify5 n) )) s) (zip [n..] lines)
           --Makes sure line number and colon are exactly 5 characters long:
           justify5 :: Int -> String
           justify5 num = if n <= 4 then s ++ ":" ++ (replicate (4 - n) ' ') else "x" ++ (drop (n - 3) s) ++ ":"
             where
               s = show num
               n = length s
           -- Replace tabs with eight spaces, to match alex:
           replaceTabs :: String -> String
           replaceTabs [] = []
           replaceTabs ('\t':ss) = (replicate 8 ' ') ++ replaceTabs ss
           replaceTabs (s:ss) = (s : replaceTabs ss)

dieIO (_,s) = printError s

printError :: String -> a
printError s = error $ "Error: " ++ s ++ "\n"

-- | Print out a list of warnings
showWarnings ::  MonadIO m => [WarningReport] -> m ()
showWarnings = mapM_ printWarning
  where
    printWarning (Just m, s) = liftIO $ hPutStrLn stderr $ show m ++ " " ++ s
    printWarning (Nothing, s) = liftIO $ hPutStrLn stderr s


-- | Fail after an internal error.
dieInternal :: Monad m => ErrorReport -> m a
dieInternal (m,s) = error $ "\n\n" ++ (maybe "" show m) ++ "Internal error: " ++ s

-- | Extract a value from a Maybe type, dying with the given error if it's Nothing.
checkJust :: Die m => ErrorReport -> Maybe t -> m t
checkJust _ (Just v) = return v
checkJust err _ = dieReport err
