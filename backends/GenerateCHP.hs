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
--
-- These are the things that need to be done before the AST reaches this backend:
--
-- Need to convert anything that isn't a communication/PAR/ALT into a Continuation
-- Passing Style (CPS).  WHILEs become IFs in recursive PROCs.  SEQ replicators become
-- recursive PROCs.
--
-- Eventually, the code passed here should have only the following in SEQ blocks:
-- 
-- * Communications
--
-- * ALTs
--
-- * PARs
--
-- * assignments (from variables or function calls)
--
-- * process calls
--
-- It should never have SEQs nested in SEQs
module GenerateCHP where

import Control.Monad.State
import Control.Monad.Trans
import Data.Char
import Data.Generics
import Data.List
import System.IO
import Text.Printf

import qualified AST as A
import CompState
import Errors
import EvalLiterals
import Metadata
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
genName n = let unders = [if c == '.' then '_' else c | c <- A.nameName n] in
  -- Prefix underscore to anything beginning with upper-case:
  if isUpper (head unders)
    then tell ["_",unders]
    else tell [unders]


genMissing = flip genMissing' ()

genMissing' :: Data a => String -> a -> CGen()
genMissing' s x = tell ["(error \"",s,": ", showConstr $ toConstr x,"\")"] -- for now, everthing is missing!
  -- TODO in future generate a Die error

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
genAST = genStructured False return

genStructured :: Data a => Bool -> (a -> CGen()) -> A.Structured a -> CGen ()
genStructured False genOnly (A.Spec m spec scope)
  = do genSpec spec
       genStructured False genOnly scope
genStructured True genOnly (A.Spec m spec scope)
  = do tell ["let "]
       withIndent $ genSpec spec
       tell ["in "]
       withIndent $ genStructured True genOnly scope
genStructured addLet genOnly (A.ProcThen m proc scope) = genMissing "genStructured ProcThen"
  >> tell ["λn"] >> genStructured addLet genOnly scope
genStructured _ genOnly (A.Only m item) = genOnly item
genStructured addLet genOnly (A.Several m strs) = mapM_ (genStructured addLet genOnly) strs

-- | Should output a spec, or nothing
genSpec :: A.Specification -> CGen ()
genSpec (A.Specification _ n (A.Proc _ _ params body))
  = do genName n
       tell [" :: "]
       mapM doFormalAndArrow params -- TODO handle return vals
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
genSpec _ = genMissing "genSpec" >> tell ["\n"]

genProcess :: A.Process -> CGen ()
genProcess (A.Seq _ str) = tell ["do "] >> withIndent (genStructured True genProcess str)
genProcess (A.ProcCall _ n params)
  = do genName n
       sequence [tell [" "] >> genActual p | p <- params]
       tell ["\n"]
genProcess p = genMissing' "genProcess" p >> tell ["\n"]

genActual :: A.Actual -> CGen ()
genActual (A.ActualVariable v) = genVariable v
genActual (A.ActualExpression e) = genExpression e

genVariable :: A.Variable -> CGen ()
genVariable (A.Variable _ n) = genName n
genVariable v = genMissing' "genVariable" v

genExpression :: A.Expression -> CGen ()
genExpression (A.Literal _ t repr)
  = do tell ["(("]
       genLiteralRepr repr
       tell [")::"]
       genType t
       tell [")"]
genExpression (A.ExprVariable _ v) = genVariable v
genExpression (A.True _) = tell ["True"]
genExpression (A.False _) = tell ["False"]
genExpression e = genMissing' "genExpression" e

seqComma :: [CGen ()] -> CGen ()
seqComma ps = sequence_ $ intersperse (tell [","]) ps

genLiteralRepr :: A.LiteralRepr -> CGen ()
genLiteralRepr (A.ArrayLiteral _ elems)
  = do tell ["newListArray (0," ++ show (length elems - 1) ++ ") ["]
       seqComma $ map genArrayElem elems
       tell ["]"]
genLiteralRepr (A.IntLiteral _ str) = tell [str]
genLiteralRepr (A.RealLiteral _ str) = tell [str]
genLiteralRepr (A.ByteLiteral m str)
  = tell ["\'"] >> genByteLiteral m str >> tell ["\'"]
genLiteralRepr _ = genMissing "genLiteralRepr"

genByteLiteral :: Meta -> String -> CGen ()
genByteLiteral m s
    =  do c <- evalByte m s
          tell [convByte c]

convByte :: Char -> String
convByte '\'' = "\\'"
convByte '"' = "\\\""
convByte '\\' = "\\\\"
convByte '\r' = "\\r"
convByte '\n' = "\\n"
convByte '\t' = "\\t"
convByte c
  | o == 0              = "\\0"
  | (o < 32 || o > 127) = printf "\\%03o" o
  | otherwise           = [c]
  where o = ord c

genArrayElem :: A.ArrayElem -> CGen ()
genArrayElem (A.ArrayElemExpr e) = genExpression e
genArrayElem _ = genMissing "genArrayElem"

genType :: A.Type -> CGen ()
genType A.Bool = tell ["Bool"]
genType A.Byte = tell ["Word8"]
genType A.UInt16 = tell ["Word16"]
genType A.UInt32 = tell ["Word32"]
genType A.UInt64 = tell ["Word64"]
genType A.Int8 = tell ["Int8"]
genType A.Int16 = tell ["Int16"]
genType A.Int = tell ["Int32"]
genType A.Int32 = tell ["Int32"]
genType A.Int64 = tell ["Int64"]
genType A.Real32 = tell ["Float"]
genType A.Real64 = tell ["Double"]
genType (A.Array _ t) = tell ["(IOUArray Int32 "] >> genType t >> tell [")"]
genType (A.List t) = tell["(Seq "] >> genType t >> tell [")"]
genType (A.Chan dir attr inner)
  = do tell ["(", case dir of
         A.DirInput -> "Chanin"
         A.DirOutput -> "Chanout"
         A.DirUnknown -> "One2OneChannel"]
       tell ["(IOUArray Word8)"]
       -- genType inner
       tell [")"]
genType _ = genMissing "genType"

--TODO compile IFs into case.  And case into case.
