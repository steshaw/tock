-- | Driver for the compiler.
module Main where

import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import List
import System
import System.Console.GetOpt
import System.IO

import Errors
import GenerateC
import Parse
import ParseState
import Pass
import PrettyShow
import SimplifyExprs
import SimplifyProcs
import Unnest

passes :: [(String, Pass)]
passes =
  [ ("Simplify expressions", simplifyExprs)
  , ("Simplify processes", simplifyProcs)
  , ("Flatten nested declarations", unnest)
  ]

type OptFunc = ParseState -> IO ParseState

options :: [OptDescr OptFunc]
options =
  [ Option [] ["parse-only"] (NoArg optParseOnly) "only parse input file"
  , Option ['v'] ["verbose"] (NoArg $ optVerboseLevel 1) "show progress information"
  , Option [] ["debug"] (NoArg $ optVerboseLevel 2) "show detailed information for debugging"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  ]

optParseOnly :: OptFunc
optParseOnly ps = return $ ps { psParseOnly = True }

optVerboseLevel :: Int -> OptFunc
optVerboseLevel n ps = return $ ps { psVerboseLevel = max (psVerboseLevel ps) n }

optOutput :: String -> OptFunc
optOutput s ps = return $ ps { psOutputFile = s }

getOpts :: [String] -> IO ([OptFunc], [String])
getOpts argv =
  case getOpt RequireOrder options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> error (concat errs ++ usageInfo header options)
  where header = "Usage: fco [OPTION...] SOURCEFILE"

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
          if psParseOnly optsPS
            then return $ show ast1
            else
              do progress "Passes:"
                 ast2 <- (runPasses passes) ast1

                 debug "{{{ Generate C"
                 progress "Generate C"
                 c <- generateC ast2
                 debug "}}}"

                 return c

        showWarnings

        case psOutputFile optsPS of
          "-" -> liftIO $ putStr output
          file ->
            do progress $ "Writing output file " ++ file
               f <- liftIO $ openFile file WriteMode
               liftIO $ hPutStr f output
               liftIO $ hClose f

        progress "Done"

