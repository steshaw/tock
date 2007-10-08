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
import Control.Monad.State
import List
import System
import System.Console.GetOpt
import System.Exit
import System.IO
import System.Process

import AnalyseAsm
import CompilerCommands
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import ParseOccam
import ParseRain
import Pass
import PreprocessOccam
import RainPasses
import SimplifyExprs
import SimplifyProcs
import SimplifyTypes
import Unnest

commonPasses :: [(String, Pass)]
commonPasses =
  [ ("Simplify types", simplifyTypes)
  , ("Simplify expressions", simplifyExprs)
  , ("Simplify processes", simplifyProcs)
  , ("Flatten nested declarations", unnest)
  ]

type OptFunc = CompState -> IO CompState

options :: [OptDescr OptFunc]
options =
  [ Option [] ["mode"] (ReqArg optMode "MODE") "select mode (options: parse, compile, post-c, full)"
  , Option [] ["backend"] (ReqArg optBackend "BACKEND") "code-generating backend (options: c, cppcsp)"
  , Option [] ["frontend"] (ReqArg optFrontend "FRONTEND") "language frontend (options: occam, rain)"
  , Option ['v'] ["verbose"] (NoArg $ optVerbose) "be more verbose (use multiple times for more detail)"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  ]

optMode :: String -> OptFunc
optMode s ps
    =  do mode <- case s of
            "parse" -> return ModeParse
            "compile" -> return ModeCompile
            "post-c" -> return ModePostC
            "full" -> return ModeFull
            _ -> dieIO (Nothing, "Unknown mode: " ++ s)
          return $ ps { csMode = mode }

optBackend :: String -> OptFunc
optBackend s ps
    =  do backend <- case s of
            "c" -> return BackendC
            "cppcsp" -> return BackendCPPCSP
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

optOutput :: String -> OptFunc
optOutput s ps = return $ ps { csOutputFile = s }

getOpts :: [String] -> IO ([OptFunc], [String])
getOpts argv =
  case getOpt RequireOrder options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> error (concat errs ++ usageInfo header options)
  where header = "Usage: tock [OPTION...] SOURCEFILE"

main :: IO ()
main = do
  argv <- getArgs
  (opts, args) <- getOpts argv

  let fn = case args of
              [fn] -> fn
              _ -> error "Must specify a single input file"

  initState <- foldl (>>=) (return emptyState) opts

  let operation
        = case csMode initState of
            ModeParse -> useOutputOptions (compile ModeParse fn)
            ModeCompile -> useOutputOptions (compile ModeCompile fn)
            ModePostC -> useOutputOptions (postCAnalyse fn)
                           -- TODO Delete the temporary files when we're done
                           -- TODO make sure the temporary files are deleted if, for some reason, the C/C++ compiler should fail:
                           -- First, compile the file into C/C++:
            ModeFull -> do (tempPath,tempHandle) <- liftIO $ openTempFile "." "tock-temp"
                           compile ModeCompile fn tempHandle
                           liftIO $ hClose tempHandle

                           optsPS <- get
                           destBin <- case csOutputFile optsPS of
                                        "-" -> error "Must specify an output file when using full-compile mode"
                                        file -> return file

                           -- Then, compile the C/C++:
                           case csBackend optsPS of
                             BackendC -> do exec $ cCommand tempPath (tempPath ++ ".o")
                                            exec $ cAsmCommand tempPath (tempPath ++ ".s")
                                            (tempPathPost, tempHandlePost) <- liftIO $ openTempFile "." "tock-temp-post"
                                            postCAnalyse (tempPath ++ ".s") tempHandlePost
                                            liftIO $ hClose tempHandlePost
                                            exec $ cCommand tempPathPost (tempPathPost ++  ".o")
                                            exec $ krocLinkCommand (tempPath ++ ".o") (tempPathPost ++ ".o") destBin
                             BackendCPPCSP -> exec $ cxxCommand tempPath destBin
                           

  -- Run the compiler.
  v <- evalStateT (runErrorT operation) initState
  case v of
    Left e -> dieIO e
    Right r -> return ()
  
  where
    exec :: String -> PassM ()
    exec cmd = do progress $ "Executing command: " ++ cmd
                  p <- liftIO $ runCommand cmd
                  exitCode <- liftIO $ waitForProcess p
                  case exitCode of
                    ExitSuccess -> return ()
                    ExitFailure n -> error $ "Command \"" ++ cmd ++ "\" failed, exiting with code: " ++ show n


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
          FrontendRain -> parseRainProgram fn
        debugAST ast1
        debug "}}}"

        showWarnings

        output <-
          case mode of
            ModeParse -> return $ show ast1
            ModeCompile ->
              do progress "Passes:"

                 let passes
                       = concat [ if csFrontend optsPS == FrontendRain
                                    then rainPasses
                                    else []
                                , commonPasses
                                , if csBackend optsPS == BackendC
                                    then genCPasses
                                    else []
                                ]
                 ast2 <- runPasses passes ast1

                 debug "{{{ Generate code"
                 let generator
                       = case csBackend optsPS of
                           BackendC -> generateC
                           BackendCPPCSP -> generateCPPCSP
                 code <- generator ast2
                 debug "}}}"

                 return code

        showWarnings

        liftIO $ hPutStr outHandle output

        progress "Done"

-- | Analyse an assembly file.
postCAnalyse :: String -> Handle -> PassM ()
postCAnalyse fn outHandle
    =  do asm <- liftIO $ readFile fn

          progress "Analysing assembly"
          output <- analyseAsm asm

          showWarnings

          liftIO $ hPutStr outHandle output

