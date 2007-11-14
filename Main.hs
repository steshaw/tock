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
import Data.Either
import Data.Generics
import Data.Maybe
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
import PreprocessOccam
import PrettyShow
import RainPasses
import SimplifyComms
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
  , ("Simplify communications", simplifyComms)
  ]

type OptFunc = CompState -> IO CompState

options :: [OptDescr OptFunc]
options =
  [ Option [] ["mode"] (ReqArg optMode "MODE") "select mode (options: flowgraph, parse, compile, post-c, full)"
  , Option [] ["backend"] (ReqArg optBackend "BACKEND") "code-generating backend (options: c, cppcsp)"
  , Option [] ["frontend"] (ReqArg optFrontend "FRONTEND") "language frontend (options: occam, rain)"
  , Option ['v'] ["verbose"] (NoArg $ optVerbose) "be more verbose (use multiple times for more detail)"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  ]

optMode :: String -> OptFunc
optMode s ps
    =  do mode <- case s of
            "flowgraph" -> return ModeFlowGraph
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

writeOccamWrapper :: Handle -> IO ()
writeOccamWrapper h = do
  write "#INCLUDE \"cifccsp.inc\"\n"
  write "#PRAGMA EXTERNAL \"PROC C.tock.main.init (INT raddr, CHAN BYTE in?, out!, err!) = 0\"\n"
  write "#PRAGMA EXTERNAL \"PROC C.tock.main.free (VAL INT raddr) = 0\"\n"
  write "PROC kroc.main (CHAN BYTE in?, out!, err!)\n"
  write "  INT addr:\n"
  write "  SEQ\n"
  write "    C.tock.main.init (addr, in?, out!, err!)\n"
  write "    cifccsp.startprocess (addr)\n"
  write "    C.tock.main.free (addr)\n"
  write ":\n"
  where
    write = hPutStr h

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
            ModeFlowGraph -> useOutputOptions (compile ModeFlowGraph fn)
            ModeCompile -> useOutputOptions (compile ModeCompile fn)
            ModePostC -> useOutputOptions (postCAnalyse fn)
            ModeFull -> evalStateT (compileFull fn) []

  -- Run the compiler.
  v <- evalStateT (runErrorT operation) initState
  case v of
    Left e -> dieIO e
    Right r -> return ()

removeFiles :: [FilePath] -> IO ()
removeFiles = mapM_ (\file -> catch (removeFile file) doNothing)
  where
    doNothing :: IOError -> IO ()
    doNothing _ = return ()

-- When we die inside the StateT [FilePath] monad, we should delete all the temporary files listed in the state, then die in the PassM monad:
-- TODO Not totally sure this technique works if functions inside the PassM monad die, but there will only be temp files to clean up if postCAnalyse dies
instance Die (StateT [FilePath] PassM) where
  dieReport err = do files <- get
                     -- If removing the files fails, we don't want to die with that error; we want the user to see the original error,
                     -- so ignore errors arising from removing the files:
                     liftIO $ removeFiles files
                     lift $ dieReport err

compileFull :: String -> StateT [FilePath] PassM ()
compileFull fn        = do optsPS <- lift get
                           destBin <- case csOutputFile optsPS of
                                        "-" -> die "Must specify an output file when using full-compile mode"
                                        file -> return file

                           -- First, compile the code into C/C++:
                           tempCPath <- execWithTempFile "tock-temp-c" (compile ModeCompile fn)

                           -- Then, compile the C/C++:
                           case csBackend optsPS of
                                            -- Compile the C into an object file:
                             BackendC -> do exec $ cCommand tempCPath (tempCPath ++ ".o")
                                            noteFile (tempCPath ++ ".o")
                                            -- Compile the same C into assembly:
                                            exec $ cAsmCommand tempCPath (tempCPath ++ ".s")
                                            noteFile (tempCPath ++ ".s")
                                            -- Analyse the assembly for stack sizes, and output a "post" C file:
                                            tempCPathPost <- execWithTempFile "tock-temp-post-c" (postCAnalyse (tempCPath ++ ".s"))
                                            -- Compile this new "post" C file into an object file:
                                            exec $ cCommand tempCPathPost (tempCPathPost ++  ".o")
                                            noteFile (tempCPathPost ++  ".o")
                                            -- Create a temporary occam file, and write the standard occam wrapper into it:
                                            tempPathOcc <- execWithTempFile "tock-temp-occ.occ" (liftIO . writeOccamWrapper)
                                            -- Use kroc to compile and link the occam file with the two object files from the C compilation:
                                            exec $ krocLinkCommand tempPathOcc [(tempCPath ++ ".o"),(tempCPathPost ++ ".o")] destBin
                                            
                                            -- For C++, just compile the source file directly into a binary:
                             BackendCPPCSP -> exec $ cxxCommand tempCPath destBin
                           
                           -- Finally, remove the temporary files:
                           tempFiles <- get
                           liftIO $ removeFiles tempFiles
    
  where
    noteFile :: Monad m => FilePath -> StateT [FilePath] m ()
    noteFile fp = modify (\fps -> (fp:fps))
  
    -- Takes a temporary file pattern, a function to do something with that file, and returns the path of the now-closed temporary file
    execWithTempFile' :: String -> (Handle -> PassM ()) -> PassM FilePath
    execWithTempFile' pat func
      = do (path,handle) <- liftIO $ openTempFile "." pat
           func handle
           liftIO $ hClose handle
           return path
    
    execWithTempFile :: String -> (Handle -> PassM ()) -> StateT [FilePath] PassM FilePath
    execWithTempFile pat func
      = do file <- lift $ execWithTempFile' pat func
           noteFile file
           return file
             
    exec :: String -> StateT [FilePath] PassM ()
    exec cmd = do lift $ progress $ "Executing command: " ++ cmd
                  p <- liftIO $ runCommand cmd
                  exitCode <- liftIO $ waitForProcess p
                  case exitCode of
                    ExitSuccess -> return ()
                    ExitFailure n -> die $ "Command \"" ++ cmd ++ "\" failed, exiting with code: " ++ show n

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
            ModeParse -> return $ pshow ast1
            ModeFlowGraph ->
              do procs <- findAllProcesses
                 let fs :: Data t => t -> PassM String
                     fs = ((liftM $ (take 20) . (filter ((/=) '\"'))) . pshowCode)
                 let labelFuncs = GLF fs fs fs fs fs fs
                 graphs <- mapM
                      ((liftM $ either (const Nothing) Just) . (buildFlowGraph labelFuncs) )
                      (map (A.OnlyP emptyMeta) (snd $ unzip $ procs))
                      
                 -- We need this line to enforce the type of the mAlter monad (Identity)
                 -- since it is never used.  Then we used graphsTyped (rather than graphs)
                 -- to prevent a compiler warning at graphsTyped being unused;
                 -- graphs is of course identical to graphsTyped, as you can see here:
                 let (graphsTyped :: [Maybe (FlowGraph Identity String)]) = graphs
                 --TODO output each process to a separate file, rather than just taking the first:
                 return $ head $ map makeFlowGraphInstr (catMaybes graphsTyped)

            ModeCompile ->
              do progress "Passes:"

                 let passes
                       = concat [ if csFrontend optsPS == FrontendRain
                                    then rainPasses
                                    else []
                                , commonPasses
                                , case csBackend optsPS of
                                    BackendC -> genCPasses
                                    BackendCPPCSP -> genCPPCSPPasses
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

