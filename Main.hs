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

-- | Driver for the compiler.
module Main (main) where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Data.Either
import Data.Generics
import Data.Maybe
import qualified Data.Set as Set
import List
import System
import System.Console.GetOpt
import System.Directory
import System.Exit
import System.IO
import System.Process

import AnalyseAsm
import qualified AST as A
import CompilerCommands
import CompState
import Errors
import FlowGraph
import GenerateC
import GenerateCPPCSP
import Metadata
import ParseOccam
import ParseRain
import Pass
import PassList
import PreprocessOccam
import PrettyShow
import ShowCode
import Utils

type OptFunc = CompState -> IO CompState

optionsNoWarnings :: [OptDescr OptFunc]
optionsNoWarnings =
  [ Option [] ["backend"] (ReqArg optBackend "BACKEND")
      "code-generating backend (options: c, cppcsp, dumpast, src)"
  , Option ['h'] ["help"] (NoArg optPrintHelp) "print this help"
  , Option [] ["help-warnings"] (NoArg optPrintWarningHelp)
      "print help about warning options"
  , Option ['k'] ["keep-temporaries"] (NoArg $ optKeepTemporaries) "keep temporary files"
  , Option [] ["frontend"] (ReqArg optFrontend "FRONTEND") "language frontend (options: occam, rain)"
  , Option [] ["mode"] (ReqArg optMode "MODE") "select mode (options: flowgraph, parse, compile, post-c, full)"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  , Option [] ["sanity-check"] (ReqArg optSanityCheck "SETTING") "internal sanity check (options: on, off)"
  , Option [] ["occam2-mobility"] (ReqArg optClassicOccamMobility "SETTING") "occam2 implicit mobility (EXPERIMENTAL) (options: on, off)"
  , Option [] ["usage-checking"] (ReqArg optUsageChecking "SETTING") "usage checking (options: on, off)"
  , Option ['v'] ["verbose"] (NoArg $ optVerbose) "be more verbose (use multiple times for more detail)"
  ]

optionsWarnings :: [OptDescr OptFunc]
optionsWarnings = concat
  [[Option [] ["w" ++ show w] (NoArg $ optEnableWarning w)
      ("Enable warning " ++ show w ++ " (" ++ describeWarning w ++ ")")]
   ++ [Option [] ["wno" ++ show w] (NoArg $ optDisableWarning w)
      ("Disable warning " ++ show w ++ " (" ++ describeWarning w ++ ")")]
  | w <- [minBound .. maxBound]]

optMode :: String -> OptFunc
optMode s ps
    =  do mode <- case s of
            "compile" -> return ModeCompile
            "flowgraph" -> return ModeFlowGraph
            "full" -> return ModeFull
            "parse" -> return ModeParse
            "post-c" -> return ModePostC
            _ -> dieIO (Nothing, "Unknown mode: " ++ s)
          return $ ps { csMode = mode }

optBackend :: String -> OptFunc
optBackend s ps
    =  do backend <- case s of
            "c" -> return BackendC
            "cppcsp" -> return BackendCPPCSP
            "dumpast" -> return BackendDumpAST
            "src" -> return BackendSource
            _ -> dieIO (Nothing, "Unknown backend: " ++ s)
          return $ ps { csBackend = backend }

optFrontend :: String -> OptFunc
optFrontend s ps
    =  do frontend <- case s of
            "occam" -> return FrontendOccam
            "rain" -> return FrontendRain
            _ -> dieIO (Nothing, "Unknown frontend: " ++ s)
          return $ ps { csFrontend = frontend }

optVerbose :: OptFunc
optVerbose ps = return $ ps { csVerboseLevel = csVerboseLevel ps + 1 }

optKeepTemporaries :: OptFunc
optKeepTemporaries ps = return $ ps { csKeepTemporaries = True }

optOutput :: String -> OptFunc
optOutput s ps = return $ ps { csOutputFile = s }

optPrintHelp :: OptFunc
optPrintHelp _ = dieIO (Nothing, usageInfo "Usage: tock [OPTION...] SOURCEFILE" optionsNoWarnings)

optPrintWarningHelp :: OptFunc
optPrintWarningHelp _ = dieIO (Nothing, usageInfo "Usage: tock [OPTION...] SOURCEFILE" optionsWarnings)

optOnOff :: (String, Bool -> CompState -> CompState) -> String -> OptFunc
optOnOff (n, f) s ps
    =  do mode <- case s of
            "on" -> return True
            "off" -> return False
            _ -> dieIO (Nothing, "Unknown " ++ n ++ " mode: " ++ s)
          return $ f mode ps

optUsageChecking :: String -> OptFunc
optUsageChecking = optOnOff ("usage checking", \m ps -> ps { csUsageChecking = m })

optSanityCheck :: String -> OptFunc
optSanityCheck = optOnOff ("sanity checking", \m ps -> ps { csSanityCheck = m })

optClassicOccamMobility :: String -> OptFunc
optClassicOccamMobility = optOnOff ("occam 2 mobility", \m ps -> ps { csClassicOccamMobility = m })

optEnableWarning :: WarningType -> OptFunc
optEnableWarning w ps = return $ ps { csEnabledWarnings = Set.insert w (csEnabledWarnings ps) }

optDisableWarning :: WarningType -> OptFunc
optDisableWarning w ps = return $ ps { csEnabledWarnings = Set.delete w (csEnabledWarnings ps) }


getOpts :: [String] -> IO ([OptFunc], [String])
getOpts argv =
  case getOpt RequireOrder (optionsNoWarnings ++ optionsWarnings) argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> error (concat errs ++ usageInfo header optionsNoWarnings)
  where header = "Usage: tock [OPTION...] SOURCEFILE"

main :: IO ()
main = do
  argv <- getArgs
  (opts, args) <- getOpts argv

  let fn = case args of
              [fn] -> fn
              _ -> error "Must specify a single input file (use \"tock --help\" to see options)"

  -- Try to guess the filename from the extension.  Since this function is
  -- applied before the options are applied, it will be overriden by the
  -- --frontend=x command-line option
  let (frontendGuess, fileStem)
                    = if ".occ" `isSuffixOf` fn
                        then (\ps -> ps {csFrontend = FrontendOccam},
                              Just $ take (length fn - length ".occ") fn)
                        else if ".rain" `isSuffixOf` fn
                          then (\ps -> ps {csFrontend = FrontendRain},
                                Just $ take (length fn - length ".rain") fn)
                          else (id, Nothing)

  initState <- foldl (>>=) (return $ frontendGuess emptyState) opts

  let operation
        = case csMode initState of
            ModeParse -> useOutputOptions (compile ModeParse fn)
            ModeFlowGraph -> useOutputOptions (compile ModeFlowGraph fn)
            ModeCompile -> useOutputOptions (compile ModeCompile fn)
            ModePostC -> useOutputOptions (postCAnalyse fn)
            ModeFull -> evalStateT (compileFull fn fileStem) []

  -- Run the compiler.
  v <- runPassM initState operation
  case v of
    (Left e, cs) -> showWarnings (csWarnings cs) >> dieIO e
    (Right r, cs) -> showWarnings (csWarnings cs)

removeFiles :: [FilePath] -> IO ()
removeFiles = mapM_ (\file -> catch (removeFile file) doNothing)
  where
    doNothing :: IOError -> IO ()
    doNothing _ = return ()

-- When we die inside the StateT [FilePath] monad, we should delete all the
-- temporary files listed in the state, then die in the PassM monad:
-- TODO: Not totally sure this technique works if functions inside the PassM
-- monad die, but there will only be temp files to clean up if postCAnalyse
-- dies
instance Die (StateT [FilePath] PassM) where
  dieReport err
      =  do files <- get
            -- If removing the files fails, we don't want to die with that
            -- error; we want the user to see the original error, so ignore
            -- errors arising from removing the files:
            optsPS <- lift $ getCompState
            when (not $ csKeepTemporaries optsPS) $
              liftIO $ removeFiles files
            lift $ dieReport err

compileFull :: String -> Maybe String -> StateT [FilePath] PassM ()
compileFull inputFile moutputFile
    =  do optsPS <- lift get
          outputFile <- case (csOutputFile optsPS, moutputFile) of
                          -- If the user hasn't given an output file, we guess by
                          -- using a stem (input file minus known extension).
                          -- If the extension isn't known, the user must specify
                          -- the output file
                          ("-", Just file) -> return file
                          ("-", Nothing) -> dieReport (Nothing, "Must specify an output file when using full-compile mode")
                          (file, _) -> return file

          let extension = case csBackend optsPS of
                            BackendC -> ".c"
                            BackendCPPCSP -> ".cpp"
                            _ -> ""

          -- Translate input file to C/C++
          let cFile = outputFile ++ extension
          withOutputFile cFile $ compile ModeCompile inputFile
          noteFile cFile

          case csBackend optsPS of
            BackendC ->
              let sFile = outputFile ++ ".s"
                  oFile = outputFile ++ ".o"
                  postCFile = outputFile ++ "_post.c"
                  postOFile = outputFile ++ "_post.o"
                  occFile = outputFile ++ "_wrapper.occ"
              in
              do sequence_ $ map noteFile [sFile, oFile, postCFile, postOFile, occFile]

                 -- Compile the C into assembly, and assembly into an object file
                 exec $ cAsmCommand cFile sFile
                 exec $ cCommand sFile oFile
                 -- Analyse the assembly for stack sizes, and output a
                 -- "post" C file
                 withOutputFile postCFile $ postCAnalyse sFile
                 -- Compile this new "post" C file into an object file
                 exec $ cCommand postCFile postOFile
                 -- Link the object files into a binary
                 exec $ cLinkCommand [oFile, postOFile] outputFile

            -- For C++, just compile the source file directly into a binary
            BackendCPPCSP ->
              exec $ cxxCommand cFile outputFile

            _ -> dieReport (Nothing, "Cannot use specified backend: "
                                     ++ show (csBackend optsPS)
                                     ++ " with full-compile mode")

          -- Finally, remove the temporary files:
          tempFiles <- get
          when (not $ csKeepTemporaries optsPS) $
            liftIO $ removeFiles tempFiles

  where
    noteFile :: Monad m => FilePath -> StateT [FilePath] m ()
    noteFile fp = modify (\fps -> (fp:fps))

    withOutputFile :: FilePath -> (Handle -> PassM ()) -> StateT [FilePath] PassM ()
    withOutputFile path func
        =  do handle <- liftIO $ openFile path WriteMode
              lift $ func handle
              liftIO $ hClose handle

    exec :: String -> StateT [FilePath] PassM ()
    exec cmd = do lift $ progress $ "Executing command: " ++ cmd
                  p <- liftIO $ runCommand cmd
                  exitCode <- liftIO $ waitForProcess p
                  case exitCode of
                    ExitSuccess -> return ()
                    ExitFailure n -> dieReport (Nothing, "Command \"" ++ cmd ++ "\" failed: exited with code: " ++ show n)

-- | Picks out the handle from the options and passes it to the function:
useOutputOptions :: (Handle -> PassM ()) -> PassM ()
useOutputOptions func
  =  do optsPS <- get
        case csOutputFile optsPS of
          "-" -> func stdout
          file ->
            do progress $ "Writing output file " ++ file
               f <- liftIO $ openFile file WriteMode
               func f
               liftIO $ hClose f

-- | Compile a file.
-- This is written in the PassM monad -- as are most of the things it calls --
-- because then it's very easy to pass the state around.
compile :: CompMode -> String -> Handle -> PassM ()
compile mode fn outHandle
  =  do optsPS <- get

        debug "{{{ Parse"
        progress "Parse"
        ast1 <- case csFrontend optsPS of
          FrontendOccam -> preprocessOccamProgram fn >>= parseOccamProgram
          FrontendRain -> liftIO (readFile fn) >>= parseRainProgram fn
        debugAST ast1
        debug "}}}"

        case mode of
            ModeParse -> liftIO $ hPutStr outHandle $ pshow ast1
            ModeFlowGraph ->
              do procs <- findAllProcesses
                 let fs :: Data t => t -> PassM String
                     fs = ((liftM $ (take 20) . (filter ((/=) '\"'))) . pshowCode)
                 let labelFuncs = mkLabelFuncsGeneric fs
                 graphs <- mapM
                      ((liftM $ either (const Nothing) Just) . (buildFlowGraphP labelFuncs) )
                      (map (A.Only emptyMeta) (snd $ unzip $ procs))

                 -- We need this line to enforce the type of the mAlter monad (Identity)
                 -- since it is never used.  Then we used graphsTyped (rather than graphs)
                 -- to prevent a compiler warning at graphsTyped being unused;
                 -- graphs is of course identical to graphsTyped, as you can see here:
                 let (graphsTyped :: [Maybe (FlowGraph' Identity String A.Process)])
                       = map (transformMaybe $ \(x,_,_) -> x) graphs
                 -- TODO: output each process to a separate file, rather than just taking the first:
                 liftIO $ hPutStr outHandle $ head $ map makeFlowGraphInstr (catMaybes graphsTyped)
            ModeCompile ->
              do progress "Passes:"

                 passes <- calculatePassList
                 ast2 <- runPasses passes ast1

                 debug "{{{ Generate code"
                 progress $ "- Backend: " ++ (show $ csBackend optsPS)
                 let generator :: A.AST -> PassM ()
                     generator
                       = case csBackend optsPS of
                           BackendC -> generateC outHandle
                           BackendCPPCSP -> generateCPPCSP outHandle
                           BackendDumpAST -> liftIO . hPutStr outHandle . pshow
                           BackendSource -> (liftIO . hPutStr outHandle) <.< showCode
                 generator ast2
                 debug "}}}"

        progress "Done"

-- | Analyse an assembly file.
postCAnalyse :: String -> Handle -> PassM ()
postCAnalyse fn outHandle
    =  do asm <- liftIO $ readFile fn

          progress "Analysing assembly"
          output <- analyseAsm asm

          liftIO $ hPutStr outHandle output

