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
popIndent = do
  (hb, cur, _:indents) <- get
  if all (== ' ') cur
    then put (hb, replicate (head indents) ' ', indents)
    else tell ["\n"] >> popIndent

withIndent :: CGen () -> CGen ()
withIndent f = pushIndent >> f >> popIndent

genName :: A.Name -> CGen ()
genName n = tell [[if c == '.' then '_' else c | c <- A.nameName n]]

genHeader :: CGen ()
genHeader
  = tell ["import GHC.Prim\n"
         ,"import Control.Concurrent.CHP\n"
         ,"\n"
         ]

generateCHP :: Handle -> A.AST -> PassM ()
generateCHP h tr
  = flip evalStateT (Right h, "", [0]) $ genHeader >> genAST tr

genAST :: A.AST -> CGen ()
genAST = genStructured False

genStructured :: Data a => Bool -> A.Structured a -> CGen ()
genStructured False (A.Spec m spec scope)
  = do genSpec spec
       genStructured False scope
genStructured True (A.Spec m spec scope)
  = do tell ["let "]
       withIndent $ genSpec spec
       tell ["in "]
       withIndent $ genStructured True scope
genStructured addLet (A.ProcThen m proc scope) = tell ["{-genStructured-}\n"] >> genStructured addLet scope
genStructured _ (A.Only m item) = tell ["{-genStructured-}\n"]
genStructured addLet (A.Several m strs) = mapM_ (genStructured addLet) strs

-- | Should output a spec, or nothing
genSpec :: A.Specification -> CGen ()
genSpec (A.Specification _ n (A.Proc _ _ params body))
  = do genName n
       tell [" :: "]
       mapM doFormalAndArrow params
       tell [" CHP ()\n"]
       genName n
       sequence [genName pn >> tell [" "] | A.Formal _ _ pn <- params]
       tell ["= "]
       withIndent $ genProcess body
  where
    doFormalAndArrow :: A.Formal -> CGen ()
    doFormalAndArrow (A.Formal _ t _)
      = genType t >> tell [" -> "]     
genSpec (A.Specification _ n (A.Declaration _ t))
  = do genName n
       tell [" :: "]
       genType t
       tell ["\n"]
       genName n
       tell [" = error \"Variable ", A.nameName n, " used uninitialised\"\n"]
genSpec (A.Specification _ n (A.IsExpr _ _ t e))
  = do genName n
       tell [" :: "]
       genType t
       tell ["\n"]
       genName n
       tell [" = "]
       genExpression e
       tell ["\n"]
genSpec _ = tell ["{-genSpec-}\n"]

genProcess :: A.Process -> CGen ()
genProcess (A.Seq _ str) = tell ["do "] >> withIndent (genStructured True str)
genProcess _ = tell ["{-genProcess-}\n"]

genExpression :: A.Expression -> CGen ()
genExpression _ = tell ["{-genExpression-}\n"]

genType :: A.Type -> CGen ()
genType A.Int = tell ["Int#"]
genType (A.Chan dir attr inner)
  = do tell ["(", case dir of
         A.DirInput -> "Chanin"
         A.DirOutput -> "Chanout"
         A.DirUnknown -> "One2OneChannel"]
       genType inner
       tell [")"]
genType _ = tell ["({-genType-})"]
