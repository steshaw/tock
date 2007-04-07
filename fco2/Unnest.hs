module Unnest where

import qualified AST as A
import Metadata
import ParseState
import Types

unnest :: ParseState -> A.Process -> IO (ParseState, A.Process)
unnest ps ast
    =  do return (ps, ast)

