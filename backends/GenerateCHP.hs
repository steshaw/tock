{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

-- | Generate CHP code from the AST
module GenerateCHP where

import Control.Monad.State
import Control.Monad.Trans
import Data.Generics
import System.IO

import qualified AST as A
import CompState
import Errors
import Pass
import Utils

-- Borrowed from GenerateCBased, and simplified:

-- A handle/string buffer, the current line, and indent stack (push at head)
type CGen = StateT (Either [String] Handle, String, [Int]) PassM

instance Die CGen where
  dieReport err = lift $ dieReport err
  
instance CSMR CGen where
  getCompState = lift getCompState

tell :: [String] -> CGen ()
tell x = do (hb, cur, curIndent:indentStack) <- get
            let cur' = replace ("\n","\n" ++ replicate curIndent ' ') (cur++concat x)
            let (cur'', prevLines)
                  = transformPair reverse reverse $
                     span (/= '\n') (reverse cur')
            hb' <- case hb of
                Left prev -> return $ Left (prev ++ lines prevLines)
                Right h -> do liftIO $ hPutStr h prevLines
                              return hb
            put (hb, cur'', curIndent:indentStack)

pushIndent :: CGen ()
pushIndent = modify $ \(hb, cur, indents) -> (hb, cur, length cur : indents)

popIndent :: CGen ()
popIndent = modify $ \(hb, cur, _:indents) -> (hb, cur, indents)                

withIndent :: CGen () -> CGen ()
withIndent f = pushIndent >> f >> popIndent

genName :: A.Name -> CGen ()
genName n = tell [[if c == '.' then '_' else c | c <- A.nameName n]]

generateCHP :: Handle -> A.AST -> PassM ()
generateCHP h tr = do
  liftIO $ hPutStrLn h "main :: IO ()"
  liftIO $ hPutStrLn h "main = return ()"
  flip evalStateT (Right h, "", [0]) $ genAST tr

genAST :: A.AST -> CGen ()
genAST = genStructured

-- TODO do the top-level without the let..in wrappers, to easily support Rain (and
-- it makes more sense)
genStructured :: Data a => A.Structured a -> CGen ()
genStructured (A.Spec m spec scope) = genSpec spec (genStructured scope)
genStructured (A.ProcThen m proc scope) = genStructured scope
genStructured (A.Only m item) = tell ["{-ONLY-}"]
genStructured (A.Several m strs) = mapM_ genStructured strs

-- | Should output a spec of the form "let..in" or nothing
genSpec :: A.Specification -> CGen () -> CGen ()
genSpec (A.Specification _ n (A.Proc _ _ params body)) scope
  = do tell ["let "]
       pushIndent
       genName n
       tell [" :: "]
       mapM doFormalAndArrow params
       tell [" CHP ()\n"]
       genName n
       sequence [genName pn >> tell [" "] | A.Formal _ _ pn <- params]
       tell ["= do\n  "]
       pushIndent
       tell ["return ()\n"] -- TODO
       popIndent
       popIndent -- TODO use withIndent
       tell ["in "]
       withIndent scope
  where
    doFormalAndArrow :: A.Formal -> CGen ()
    doFormalAndArrow (A.Formal _ t _)
      = genType t >> tell [" -> "]     
genSpec _ scope = scope

genType :: A.Type -> CGen ()
genType _ = tell ["({-TYPE-})"]
