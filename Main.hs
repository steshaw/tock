-- | Driver for the compiler.
module Main where

import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import List
import System
import System.Console.GetOpt
import System.IO

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
  [ Option [] ["parse-only"] (NoArg optParseOnly) "only parse input file"
  , Option ['v'] ["verbose"] (NoArg $ optVerbose) "be more verbose (use multiple times for more detail)"
  , Option [] ["backend"] (ReqArg optBackend "BACKEND") "backend (options: CIF, CPPCSP)"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  ]

optParseOnly :: OptFunc
optParseOnly ps = return $ ps { csParseOnly = True }

optVerbose :: OptFunc
optVerbose ps = return $ ps { csVerboseLevel = csVerboseLevel ps + 1 }

optOutput :: String -> OptFunc
optOutput s ps = return $ ps { csOutputFile = s }

optBackend :: String -> OptFunc
optBackend s ps = return $ ps { csBackend = s }

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

  -- Run the compiler.
  v <- evalStateT (runErrorT (compile fn)) initState
  case v of
    Left e -> dieIO e
    Right r -> return ()

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
          if csParseOnly optsPS
            then return $ show ast1
            else
              do progress "Passes:"
                 ast2 <- (runPasses passes) ast1

                 debug "{{{ Generate Code"
                 c <-
                   case csBackend optsPS of 
                     "CPPCSP" -> 
                       do progress "Generate C++CSP"
                          c' <- generateCPPCSP ast2
                          return c'
                     "CIF" ->
                       do progress "Generate C/CIF"
                          c' <- generateC ast2
                          return c'
                     _ -> 
                       do error ("Unknown backend: " ++ (csBackend optsPS))

                 debug "}}}"

                 return c

        showWarnings

        case csOutputFile optsPS of
          "-" -> liftIO $ putStr output
          file ->
            do progress $ "Writing output file " ++ file
               f <- liftIO $ openFile file WriteMode
               liftIO $ hPutStr f output
               liftIO $ hClose f

        progress "Done"

