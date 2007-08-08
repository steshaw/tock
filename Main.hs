-- | Driver for the compiler.
module Main where

import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import List
import System
import System.Console.GetOpt
import System.IO

import AnalyseAsm
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import Parse
import Pass
import PrettyShow
import SimplifyExprs
import SimplifyProcs
import SimplifyTypes
import Unnest

passes :: [(String, Pass)]
passes =
  [ ("Simplify types", simplifyTypes)
  , ("Simplify expressions", simplifyExprs)
  , ("Simplify processes", simplifyProcs)
  , ("Flatten nested declarations", unnest)
  ]

type OptFunc = CompState -> IO CompState

options :: [OptDescr OptFunc]
options =
  [ Option [] ["mode"] (ReqArg optMode "MODE") "select mode (options: parse, compile, post-c)"
  , Option [] ["backend"] (ReqArg optBackend "BACKEND") "code-generating backend (options: c, cppcsp)"
  , Option ['v'] ["verbose"] (NoArg $ optVerbose) "be more verbose (use multiple times for more detail)"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  ]

optMode :: String -> OptFunc
optMode s ps
    =  do mode <- case s of
            "parse" -> return ModeParse
            "compile" -> return ModeCompile
            "post-c" -> return ModePostC
            _ -> dieIO $ "Unknown mode: " ++ s
          return $ ps { csMode = mode }

optBackend :: String -> OptFunc
optBackend s ps
    =  do backend <- case s of
            "c" -> return BackendC
            "cppcsp" -> return BackendCPPCSP
            _ -> dieIO $ "Unknown backend: " ++ s
          return $ ps { csBackend = backend }

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
            ModeParse -> compile fn
            ModeCompile -> compile fn
            ModePostC -> postCAnalyse fn

  -- Run the compiler.
  v <- evalStateT (runErrorT operation) initState
  case v of
    Left e -> dieIO e
    Right r -> return ()

-- | Write the output to the file the user wanted.
writeOutput :: String -> PassM ()
writeOutput output
  =  do optsPS <- get
        case csOutputFile optsPS of
          "-" -> liftIO $ putStr output
          file ->
            do progress $ "Writing output file " ++ file
               f <- liftIO $ openFile file WriteMode
               liftIO $ hPutStr f output
               liftIO $ hClose f

-- | Compile a file.
-- This is written in the PassM monad -- as are most of the things it calls --
-- because then it's very easy to pass the state around.
compile :: String -> PassM ()
compile fn
  =  do optsPS <- get

        debug "{{{ Preprocess"
        loadSource fn
        debug "}}}"

        debug "{{{ Parse"
        progress "Parse"
        ast1 <- parseProgram fn
        debugAST ast1
        debug "}}}"

        showWarnings

        output <-
          case csMode optsPS of
            ModeParse -> return $ show ast1
            ModeCompile ->
              do progress "Passes:"
                 ast2 <- (runPasses passes) ast1

                 debug "{{{ Generate code"
                 let generator
                       = case csBackend optsPS of
                           BackendC -> generateC
                           BackendCPPCSP -> generateCPPCSP
                 code <- generator ast2
                 debug "}}}"

                 return code

        showWarnings

        writeOutput output

        progress "Done"

-- | Analyse an assembly file.
postCAnalyse :: String -> PassM ()
postCAnalyse fn
    =  do asm <- liftIO $ readSource fn

          progress "Analysing assembly"
          output <- analyseAsm asm

          showWarnings

          writeOutput output

