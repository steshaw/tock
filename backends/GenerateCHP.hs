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
popIndent = modify $ \(hb, cur, _:indents) ->
  if all (== ' ') cur
    then (hb, replicate (head indents) ' ', indents)
    else (hb, cur, indents)                

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
       genSpec spec
       tell ["in "]
       withIndent $ genStructured True scope
genStructured addLet (A.ProcThen m proc scope) = genStructured addLet scope
genStructured _ (A.Only m item) = tell ["{-ONLY-}"]
genStructured addLet (A.Several m strs) = mapM_ (genStructured addLet) strs

-- | Should output a spec, or nothing
genSpec :: A.Specification -> CGen ()
genSpec (A.Specification _ n (A.Proc _ _ params body))
  = withIndent $ do
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
  where
    doFormalAndArrow :: A.Formal -> CGen ()
    doFormalAndArrow (A.Formal _ t _)
      = genType t >> tell [" -> "]     
genSpec _ = return ()

genType :: A.Type -> CGen ()
genType A.Int = tell ["Int#"]
genType (A.Chan dir attr inner)
  = do tell ["(", case dir of
         A.DirInput -> "Chanin"
         A.DirOutput -> "Chanout"
         A.DirUnknown -> "One2OneChannel"]
       genType inner
       tell [")"]
genType _ = tell ["({-TYPE-})"]
