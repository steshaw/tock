{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

-- | Generate C code from the mangled AST.  Most of the exports here are actually
-- for GenerateCPPCSP to use
module GenerateC
  ( cgenOps
  , cgenReplicatorLoop
  , cgetCType
  , cintroduceSpec
  , cPreReq
  , cremoveSpec
  , genCPasses
  , genDynamicDim
  , generate
  , generateC
  , genLeftB
  , genMeta
  , genName
  , genRightB
  , genStatic
  , nameString
  , needStackSizes
  , justOnly
  , withIf
  ) where

import Data.Char
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Control.Monad.State
import System.IO
import Text.Printf

import qualified AST as A
import BackendPasses
import CompState
import Errors
import EvalConstants
import EvalLiterals
import Intrinsics
import GenerateCBased
import Metadata
import Pass
import qualified Properties as Prop
import ShowCode
import TLP
import Types
import TypeSizes
import Utils

--{{{  passes related to C generation
genCPasses :: [Pass]
genCPasses = [transformWaitFor]
--}}}

cPreReq :: [Property]
cPreReq = cCppCommonPreReq ++ [Prop.parsIdentified, Prop.waitForRemoved]

--{{{  generator ops
-- | Operations for the C backend.
cgenOps :: GenOps
cgenOps = GenOps {
    declareFree = cdeclareFree,
    declareInit = cdeclareInit,
    genActual = cgenActual,
    genActuals = cgenActuals,
    genAlt = cgenAlt,
    genAllocMobile = cgenAllocMobile,
    genArrayLiteralElems = cgenArrayLiteralElems,
    genArrayStoreName = genName,
    genArraySubscript = cgenArraySubscript,
    genAssert = cgenAssert,
    genAssign = cgenAssign,
    genBytesIn = cgenBytesIn,
    genCase = cgenCase,
    genCheckedConversion = cgenCheckedConversion,
    genClearMobile = cgenClearMobile,
    genCloneMobile = cgenCloneMobile,
    genConversion = cgenConversion,
    genConversionSymbol = cgenConversionSymbol,
    getCType = cgetCType,
    genDecl = cgenDecl,
    genDeclaration = cgenDeclaration,
    genDirectedVariable = cgenDirectedVariable,
    genDyadic = cgenDyadic,
    genExpression = cgenExpression,
    genFlatArraySize = cgenFlatArraySize,
    genForwardDeclaration = cgenForwardDeclaration,
    genFuncDyadic = cgenFuncDyadic,
    genFuncMonadic = cgenFuncMonadic,
    genGetTime = cgenGetTime,
    genIf = cgenIf,
    genInput = cgenInput,
    genInputItem = cgenInputItem,
    genIntrinsicFunction = cgenIntrinsicFunction,
    genIntrinsicProc = cgenIntrinsicProc,
    genListAssign = cgenListAssign,
    genListConcat = cgenListConcat,
    genListLiteral = cgenListLiteral,
    genListSize = cgenListSize,
    genLiteral = cgenLiteral,
    genLiteralRepr = cgenLiteralRepr,
    genMissing = cgenMissing,
    genMissingC = (\x -> x >>= cgenMissing),
    genMonadic = cgenMonadic,
    genOutput = cgenOutput,
    genOutputCase = cgenOutputCase,
    genOutputItem = cgenOutputItem,
    genOverArray = cgenOverArray,
    genPar = cgenPar,
    genProcCall = cgenProcCall,
    genProcess = cgenProcess,
    genRecordTypeSpec = cgenRecordTypeSpec,
    genReplicatorStart = cgenReplicatorStart,
    genReplicatorEnd = cgenReplicatorEnd,
    genReplicatorLoop = cgenReplicatorLoop,
    genReschedule = cgenReschedule,
    genRetypeSizes = cgenRetypeSizes,
    genSeq = cgenSeq,
    genSimpleDyadic = cgenSimpleDyadic,
    genSimpleMonadic = cgenSimpleMonadic,
    genSpec = cgenSpec,
    genSpecMode = cgenSpecMode,
    genStop = cgenStop,
    genStructured = cgenStructured,
    genTimerRead = cgenTimerRead,
    genTimerWait = cgenTimerWait,
    genTopLevel = cgenTopLevel,
    genTypeSymbol = cgenTypeSymbol,
    genUnfoldedExpression = cgenUnfoldedExpression,
    genUnfoldedVariable = cgenUnfoldedVariable,
    genVariable' = cgenVariableWithAM True,
    genVariableUnchecked = \v am -> cgenVariableWithAM False v am id,
    genWhile = cgenWhile,
    getScalarType = cgetScalarType,
    introduceSpec = cintroduceSpec,
    removeSpec = cremoveSpec
  }
--}}}

--{{{  top-level
generateC :: (Handle, Handle) -> String -> A.AST -> PassM ()
generateC = generate cgenOps

needStackSizes :: (CSMR m, Die m) => m [A.Name]
needStackSizes
  = do cs <- getCompState
       return $ nub $ ([A.Name emptyMeta $ nameString $ A.Name emptyMeta n
                       | A.NameDef {A.ndName = n
                                   ,A.ndSpecType=A.Proc {}
                                   } <- Map.elems $ csNames cs]
                      )
                      \\ (map (A.Name emptyMeta . nameString . A.Name emptyMeta . fst) (csExternals cs))

cgenTopLevel :: String -> A.AST -> CGen ()
cgenTopLevel headerName s
    =  do tell ["#define occam_INT_size ", show cIntSize,"\n"]
          tell ["#include <tock_support_cif.h>\n"]
          cs <- getCompState

          let isTopLevelSpec (A.Specification _ n _)
                = A.nameName n `elem` (csOriginalTopLevelProcs cs)

          tellToHeader $ sequence_ $ map (call genForwardDeclaration)
                                       (listify isTopLevelSpec s)
          -- Things like lifted wrapper_procs we still need to forward-declare,
          -- but we do it in the C file, not in the header:
          sequence_ $ map (call genForwardDeclaration)
                            (listify (not . isTopLevelSpec) s)

          tell ["#include \"", dropPath headerName, "\"\n"]

          sequence_ [tell ["#include \"", usedFile, ".tock.h\"\n"]
                    | usedFile <- Set.toList $ csUsedFiles cs]

          nss <- needStackSizes
          sequence_ [tell ["extern int "] >> genName n >> tell ["_stack_size;\n"]
                     | n <- nss]

          when (csHasMain cs) $ do
            (tlpName, tlpChans) <- tlpInterface
            tell ["extern int "]
            genName tlpName
            tell ["_stack_size;\n"]

          -- Forward declarations of externals:
          sequence_ [tell ["extern void ", mungeExternalName n, "(int*);"]
                    | (n, (ExternalOldStyle, _)) <- csExternals cs]

          call genStructured TopLevel s (\m _ -> tell ["\n#error Invalid top-level item: ", show m])

          when (csHasMain cs) $ do
            (tlpName, tlpChans) <- tlpInterface
            chans <- sequence [csmLift $ makeNonce emptyMeta "tlp_channel" | _ <- tlpChans]
            killChans <- sequence [csmLift $ makeNonce emptyMeta "tlp_channel_kill" | _ <- tlpChans]
            workspaces <- sequence [csmLift $ makeNonce emptyMeta "tlp_channel_ws" | _ <- tlpChans]


            tell ["void tock_main (Workspace wptr) {\n"]
            sequence_ [do tell ["    Channel ", c, ";\n"]
                          tell ["    ChanInit (wptr, &", c, ");\n"]
                      | c <- chans ++ killChans]
            tell ["\n"]

            funcs <- sequence [genTLPHandler tc c kc ws
                             | (tc, c, kc, ws) <- zip4 tlpChans chans killChans workspaces]

            tell ["    LightProcBarrier bar;\n\
                  \    LightProcBarrierInit (wptr, &bar, ", show $ length chans, ");\n"]

            sequence_ [tell ["    LightProcStart (wptr, &bar, ", ws, ", (Process) ", func, ");\n"]
                       | (ws, func) <- zip workspaces funcs]

            tell ["\n\
                   \    "]
            genName tlpName
            tell [" (wptr"]
            sequence_ [tell [", &", c] | c <- chans]
            tell [");\n\
                  \\n"]
            sequence_ [tell ["    ", func, "_kill (wptr, &", kc, ");\n"]
                       | (func, kc) <- zip funcs killChans]

            let uses_stdin = if TLPIn `elem` (map snd tlpChans) then "true" else "false"
            tell ["    LightProcBarrierWait (wptr, &bar);\n\
                  \\n\
                  \    Shutdown (wptr);\n\
                  \}\n\
                  \\n\
                  \int main (int argc, char *argv[]) {\n\
                  \    tock_init_ccsp (", uses_stdin, ");\n\
                  \\n\
                  \    Workspace p = ProcAllocInitial (0, "]
            genName tlpName
            tell ["_stack_size + 512);\n\
                  \    ProcStartInitial (p, tock_main);\n\
                  \\n\
                  \    // NOTREACHED\n\
                  \    return 0;\n\
                  \}\n"]
  where
    dropPath = reverse . takeWhile (/= '/') . reverse
    
    mungeExternalName (_:cs) = [if c == '.' then '_' else c | c <- cs]

    -- | Allocate a TLP channel handler process, and return the function that
    -- implements it.
    genTLPHandler :: (Maybe A.Direction, TLPChannel) -> String -> String -> String -> CGen String
    genTLPHandler (_, tc) c kc ws
        =  do tell ["    Workspace ", ws, " = ProcAlloc (wptr, 3, 1024);\n\
                    \    ProcParam (wptr, ", ws, ", 0, &", c, ");\n\
                    \    ProcParam (wptr, ", ws, ", 1, &", kc, ");\n\
                    \    ProcParam (wptr, ", ws, ", 2, ", fp, ");\n\
                    \\n"]
              return func
      where
        (fp, func) = case tc of
                       TLPIn -> ("stdin", "tock_tlp_input")
                       TLPOut -> ("stdout", "tock_tlp_output")
                       TLPError -> ("stderr", "tock_tlp_output")
--}}}

--{{{  utilities
cgenMissing :: String -> CGen ()
cgenMissing s = tell ["\n#error Unimplemented: ", s, "\n"]

--{{{  simple punctuation
genLeftB :: CGen ()
genLeftB = tell ["{"]

genRightB :: CGen ()
genRightB = tell ["}"]
--}}}

-- | Map an operation over every item of an occam array.
cgenOverArray :: Meta -> A.Variable -> (SubscripterFunction -> Maybe (CGen ())) -> CGen ()
cgenOverArray m var func
    =  do A.Array ds _ <- astTypeOf var
          specs <- sequence [csmLift $ makeNonceVariable "i" m A.Int A.Original | _ <- ds]
          let indices = [A.Variable m n | A.Specification _ n _ <- specs]

          let arg = (\var -> foldl (\v s -> A.SubscriptedVariable m s v) var [A.Subscript m A.NoCheck $ A.ExprVariable m i | i <- indices])
          case func arg of
            Just p ->
              do sequence_ [do tell ["for(int "]
                               call genVariable i A.Original
                               tell ["=0;"]
                               call genVariable i A.Original
                               tell ["<"]
                               case d of
                                 A.UnknownDimension -> genDynamicDim var v
                                 A.Dimension n -> call genExpression n
                               tell [";"]
                               call genVariable i A.Original
                               tell ["++){"]
                            | (v :: Int, i, d) <- zip3 [0..] indices ds]
                 p
                 sequence_ [tell ["}"] | _ <- indices]
            Nothing -> return ()

-- | Generate code for one of the Structured types.
cgenStructured :: Data a => Level -> A.Structured a -> (Meta -> a -> CGen b) -> CGen [b]
cgenStructured lvl (A.Spec _ spec s) def = call genSpec lvl spec (call genStructured lvl s def)
cgenStructured lvl (A.ProcThen _ p s) def = call genProcess p >> call genStructured lvl s def
cgenStructured lvl (A.Several _ ss) def
  = sequence [call genStructured lvl s def | s <- ss] >>* concat
cgenStructured _ (A.Only m s) def = def m s >>* singleton

--}}}

--{{{  metadata
-- | Turn a Meta into a string literal that can be passed to a function
-- expecting a const char * argument.
genMeta :: Meta -> CGen ()
genMeta m = tell ["\"", show m, "\""]
--}}}

--{{{  names
nameString :: A.Name -> String
nameString n = [if c == '.' then '_' else c | c <- A.nameName n]

genName :: A.Name -> CGen ()
genName n = tell [nameString n]
--}}}

--{{{  types
-- | If a type maps to a simple C type, return Just that; else return Nothing.
cgetScalarType :: A.Type -> Maybe String
cgetScalarType A.Bool = Just "bool"
cgetScalarType A.Byte = Just "uint8_t"
cgetScalarType A.UInt16 = Just "uint16_t"
cgetScalarType A.UInt32 = Just "uint32_t"
cgetScalarType A.UInt64 = Just "uint64_t"
cgetScalarType A.Int8 = Just "int8_t"
cgetScalarType A.Int = cgetScalarType cIntReplacement
cgetScalarType A.Int16 = Just "int16_t"
cgetScalarType A.Int32 = Just "int32_t"
cgetScalarType A.Int64 = Just "int64_t"
cgetScalarType A.Real32 = Just "float"
cgetScalarType A.Real64 = Just "double"
cgetScalarType (A.Timer A.OccamTimer) = Just "Time"
cgetScalarType A.Time = Just "Time"
cgetScalarType _ = Nothing

indexOfFreeDimensions :: [A.Dimension] -> [Int]
indexOfFreeDimensions = (mapMaybe indexOfFreeDimensions') . (zip [0..])
  where
    indexOfFreeDimensions' :: (Int,A.Dimension) -> Maybe Int
    indexOfFreeDimensions' (_, A.Dimension _) = Nothing
    indexOfFreeDimensions' (n, A.UnknownDimension) = Just n


-- | Generate the number of bytes in a type.
cgenBytesIn :: Meta -> A.Type -> Either Bool A.Variable -> CGen ()
cgenBytesIn m t v
    = do  case (t, v) of
            (A.Array ds _, Left freeDimensionAllowed) ->
              case (length (indexOfFreeDimensions ds), freeDimensionAllowed) of
                (0,_) -> return ()
                (1,False) -> dieP m "genBytesIn type with unknown dimension, when unknown dimensions are not allowed"
                (1,True) -> return ()
                (_,_) -> dieP m "genBytesIn type with more than one free dimension"
            _ -> return ()
          genBytesIn' t
  where
    genBytesIn' :: A.Type -> CGen ()
    genBytesIn' (A.Array ds t)
      = do mapM_ genBytesInArrayDim (reverse $ zip ds [0..]) --The reverse is simply to match the existing tests
           genBytesIn' t

    genBytesIn' (A.Record n)
      = do tell ["sizeof("]
           genName n
           tell [")"]
    -- This is so that we can do RETYPES checks on channels; we don't actually
    -- allow retyping between channels and other things.
    genBytesIn' t@(A.Chan {})
      = do tell ["sizeof("]
           genType t
           tell [")"]
    genBytesIn' t@(A.ChanEnd {})
      = do tell ["sizeof("]
           genType t
           tell [")"]
    genBytesIn' (A.Mobile t@(A.Array {})) = genBytesIn' t
    genBytesIn' (A.Mobile _)
      = tell ["sizeof(void*)"]
    genBytesIn' (A.List _)
      = tell ["sizeof(void*)"]
    genBytesIn' t
      = do f <- fget getScalarType
           case f t of
             Just s -> tell ["sizeof(", s, ")"]
             Nothing -> diePC m $ formatCode "genBytesIn' %" t

    -- FIXME: This could be done by generating an expression for the size,
    -- which is what declareSizesPass has to do -- they should share a helper
    -- function.
    genBytesInArrayDim :: (A.Dimension,Int) -> CGen ()
    genBytesInArrayDim (A.Dimension n, _)
        =  do call genExpression n
              tell ["*"]
    genBytesInArrayDim (A.UnknownDimension, i)
        = case v of
            Right rv ->
              do genDynamicDim rv i
                 tell ["*"]
            _ -> return ()

--}}}

genStatic :: Level -> A.Name -> CGen ()
genStatic NotTopLevel _ = return ()
genStatic TopLevel n
  = do cs <- getCompState
       when (A.nameName n `notElem` csOriginalTopLevelProcs cs) $
         tell ["static "]

--{{{  declarations
cgenDecl :: Level -> A.AbbrevMode -> A.Type -> A.Name -> CGen ()
cgenDecl lvl am t n
    =  do genStatic lvl n
          genCType (A.nameMeta n) t am
          tell [" "]
          genName n
--}}}

--{{{  conversions
cgenCheckedConversion :: Meta -> A.Type -> A.Type -> CGen () -> CGen ()
cgenCheckedConversion m fromT toT exp
    =  do tell ["(("]
          genType toT
          tell [") "]
          if isSafeConversion fromT toT
            then exp
            else do call genTypeSymbol "range_check" fromT
                    tell [" ("]
                    call genTypeSymbol "mostneg" toT
                    tell [", "]
                    call genTypeSymbol "mostpos" toT
                    tell [", "]
                    exp
                    tell [", "]
                    genMeta m
                    tell [")"]
          tell [")"]

cgenConversion :: Meta -> A.ConversionMode -> A.Type -> A.Expression -> CGen ()
cgenConversion m A.DefaultConversion toT e
    =  do fromT <- astTypeOf e
          call genCheckedConversion m fromT toT (call genExpression e)
cgenConversion m cm toT e
    =  do fromT <- astTypeOf e
          case (isSafeConversion fromT toT, isRealType fromT, isRealType toT) of
            (True, _, _) ->
              -- A safe conversion -- no need for a check.
              call genCheckedConversion m fromT toT (call genExpression e)
            (_, True, True) ->
              -- Real to real.
              do call genConversionSymbol fromT toT cm
                 tell [" ("]
                 call genExpression e
                 tell [", "]
                 genMeta m
                 tell [")"]
            (_, True, False) ->
              -- Real to integer -- do real -> int64_t -> int.
              do let exp = do call genConversionSymbol fromT A.Int64 cm
                              tell [" ("]
                              call genExpression e
                              tell [", "]
                              genMeta m
                              tell [")"]
                 call genCheckedConversion m A.Int64 toT exp
            (_, False, True) ->
              -- Integer to real -- do int -> int64_t -> real.
              do call genConversionSymbol A.Int64 toT cm
                 tell [" ("]
                 call genCheckedConversion m fromT A.Int64 (call genExpression e)
                 tell [", "]
                 genMeta m
                 tell [")"]
            _ -> call genMissing $ "genConversion " ++ show cm

cgenConversionSymbol :: A.Type -> A.Type -> A.ConversionMode -> CGen ()
cgenConversionSymbol fromT toT cm
    =  do tell ["occam_convert_"]
          genType fromT
          tell ["_"]
          genType toT
          tell ["_"]
          case cm of
            A.Round -> tell ["round"]
            A.Trunc -> tell ["trunc"]
--}}}

--{{{  literals
cgenLiteral :: A.LiteralRepr -> A.Type -> CGen ()
cgenLiteral lr t
    = if isStringLiteral lr
        then do tell ["\""]
                let A.ArrayListLiteral _ (A.Several _ aes) = lr
                sequence_ [genByteLiteral m s
                           | A.Only _ (A.Literal _ _ (A.ByteLiteral m s)) <- aes]
                tell ["\""]
        else call genLiteralRepr lr t

-- | Does a LiteralRepr represent something that can be a plain string literal?
isStringLiteral :: A.LiteralRepr -> Bool
isStringLiteral (A.ArrayListLiteral _ (A.Several _ aes))
    = and [case ae of
             A.Only _ (A.Literal _ _ (A.ByteLiteral _ _)) -> True
             _ -> False
           | ae <- aes]
isStringLiteral _ = False

genLitSuffix :: A.Type -> CGen ()
genLitSuffix A.UInt32 = tell ["U"]
genLitSuffix A.Int64 = tell ["LL"]
genLitSuffix A.UInt64 = tell ["ULL"]
genLitSuffix A.Real32 = tell ["F"]
genLitSuffix _ = return ()

-- TODO don't allocate for things less than 64-bits in size
cgenListLiteral :: A.Structured A.Expression -> A.Type -> CGen ()
cgenListLiteral (A.Several _ es) t
  = foldl addItem (tell ["g_queue_new()"]) [e | A.Only _ e <- es]
  where
    addItem :: CGen () -> A.Expression -> CGen ()
    addItem prev add
      = do tell ["g_queue_push_head("]
           prev
           tell [","]
           call genExpression add
           tell [")"]

cgenListSize :: A.Variable -> CGen ()
cgenListSize v = do tell ["g_queue_get_length("]
                    call genVariable v A.Original
                    tell [")"]

cgenListAssign :: A.Variable -> A.Expression -> CGen ()
cgenListAssign v e
  = do tell ["tock_free_queue("]
       call genVariable v A.Original
       tell [");"]
       call genVariable v A.Original
       tell ["="]
       call genExpression e
       tell [";"]

cgenLiteralRepr :: A.LiteralRepr -> A.Type -> CGen ()
cgenLiteralRepr (A.RealLiteral m s) t
  | "Infinity" `isPrefixOf` s = tell ["INFINITY"]
  | "NaN" `isPrefixOf` s = tell ["NAN"]
  | otherwise = tell [s] >> genLitSuffix t
cgenLiteralRepr (A.IntLiteral m s) t
  = do genDecimal s
       genLitSuffix t
cgenLiteralRepr (A.HexLiteral m s) t
  = do f <- fget getScalarType
       ct <- case f t of
         Just ct -> return ct
         Nothing -> diePC m $ formatCode "Non-scalar type for hex literal: " t
       tell ["((",ct,")0x", s]
       genLitSuffix t
       tell [")"]
cgenLiteralRepr (A.ByteLiteral m s) _
    = tell ["'"] >> genByteLiteral m s >> tell ["'"]
cgenLiteralRepr (A.RecordLiteral _ es) _
    =  do genLeftB
          seqComma $ map (call genUnfoldedExpression) es
          genRightB
cgenLiteralRepr (A.ArrayListLiteral m aes) (A.Array {})
    = genLeftB >> call genArrayLiteralElems aes >> genRightB
cgenLiteralRepr (A.ArrayListLiteral _ es) t@(A.List {})
    = call genListLiteral es t
cgenLiteralRepr (A.ArrayListLiteral m _) t
    = diePC m $ formatCode "Unknown type for array/list literal: %" t

-- | Generate an expression inside a record literal.
--
-- This is awkward: the sort of literal that this produces when there's a
-- variable in here cannot always be compiled at the top level of a C99 program
-- -- because in C99, an array subscript is not a constant, even if it's a
-- constant subscript of a constant array.  So we need to be sure that when we
-- use this at the top level, the thing we're unfolding only contains literals.
-- Yuck!
cgenUnfoldedExpression :: A.Expression -> CGen ()
cgenUnfoldedExpression (A.Literal _ t lr)
    =  do call genLiteralRepr lr t
cgenUnfoldedExpression (A.ExprVariable m var) = call genUnfoldedVariable m var
cgenUnfoldedExpression e = call genExpression e

-- | Generate a variable inside a record literal.
cgenUnfoldedVariable :: Meta -> A.Variable -> CGen ()
cgenUnfoldedVariable m var
    =  do t <- astTypeOf var
          case t of
            A.Array ds _ ->
              do genLeftB
                 unfoldArray ds var
                 genRightB
            A.Record _ ->
              do genLeftB
                 fs <- recordFields m t
                 seqComma [call genUnfoldedVariable m (A.SubscriptedVariable m (A.SubscriptField m n) var)
                           | (n, t) <- fs]
                 genRightB
            -- We can defeat the usage check here because we know it's safe; *we're*
            -- generating the subscripts.
            -- FIXME Is that actually true for something like [a[x]]?
            _ -> call genVariableUnchecked var A.Original
  where
    unfoldArray :: [A.Dimension] -> A.Variable -> CGen ()
    unfoldArray [] v = call genUnfoldedVariable m v
    unfoldArray (A.Dimension e:ds) v
      = do n <- evalIntExpression e
           seqComma $ [unfoldArray ds (A.SubscriptedVariable m (A.Subscript m A.NoCheck $ makeConstant m i) v)
                       | i <- [0..(n - 1)]]
    unfoldArray _ _ = dieP m "trying to unfold array with unknown dimension"

-- | Generate a decimal literal -- removing leading zeroes to avoid producing
-- an octal literal!
genDecimal :: String -> CGen ()
genDecimal "0" = tell ["0"]
genDecimal ('0':s) = genDecimal s
genDecimal ('-':s) = tell ["-"] >> genDecimal s
genDecimal s = tell [s]

cgenArrayLiteralElems :: A.Structured A.Expression -> CGen ()
cgenArrayLiteralElems (A.Only _ e) = call genUnfoldedExpression e
cgenArrayLiteralElems (A.Several _ aes)
    = seqComma $ map cgenArrayLiteralElems aes
cgenArrayLiteralElems x = call genMissingC $ formatCode "Missing cgenArrayLiteralElems for %" x

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
--}}}

--{{{  variables

cgenVariableWithAM :: Bool -> A.Variable -> A.AbbrevMode -> (CType -> CType) -> CGen ()
cgenVariableWithAM checkValid v am fct
  = do iv <- inner v
       t <- astTypeOf v
       ct <- call getCType m t am >>* fct
       -- Temporary, for debugging:
       -- tell ["/* ", show (snd iv), " , trying to get: ", show ct, " */"]
       dressUp m iv ct
  where
    m = findMeta v

    details :: A.Variable -> CGen CType
    details v = do t <- astTypeOf v
                   am <- abbrevModeOfVariable v
                   call getCType m t am
    
    inner :: A.Variable -> CGen (CGen (), CType)
    inner v@(A.Variable  m n)
      = do ct <- details v
           return (genName n, ct)
    inner (A.DerefVariable m v)
      = do (A.Mobile t) <- astTypeOf v
           case t of
             A.Array _ innerT ->
               do (cg, ct) <- inner v
                  innerCT <- call getCType m innerT A.Original
                  let cast = tell ["("] >> genType innerT >> tell ["*)"]
                  return (do tell ["("]
                             cast
                             tell ["(("]
                             dressUp m (cg, ct) (Pointer $ Plain "mt_array_t")
                             tell [")->data))"]
                         , Pointer $ innerCT)
             _ -> inner v
    inner wholeV@(A.DirectedVariable m dir v)
      = do (cg, _) <- inner v
           t <- astTypeOf v
           wholeT <- astTypeOf wholeV
           ct <- call getCType m wholeT A.Original
           return (call genDirectedVariable m t cg dir, ct)
    inner (A.VariableSizes m (A.Variable _ n))
      = do t <- astTypeOf n
           f <- fget getScalarType
           let Just intT = f A.Int
           case t of
             A.Mobile (A.Array {})
               -> return (do call genVariable v A.Original
                             tell ["->dimensions"]
                         , Pointer $ Plain intT)
             A.Array {}
               -> do ss <- getCompState >>* csArraySizes
                     case Map.lookup (A.nameName n) ss of
                       Just n_sizes -> return (genName n_sizes
                                              ,Pointer $ Plain intT)
                       Nothing ->
                         dieP m $ "No sizes for " ++ A.nameName n
                           ++ " -- full list: " ++ show (Map.keys ss)
    inner (A.VariableSizes m v@(A.SubscriptedVariable {}))
      = do (es, innerV, _) <- collectSubs v
           case innerV of
             plainV@(A.Variable {}) ->
               do (gen, ct) <- inner (A.VariableSizes m plainV)
                  return (do tell ["("]
                             gen
                             tell ["+", show (length es),")"]
                         ,ct)
             _ -> diePC m $ formatCode "Cannot handle complex sizes expression %" v
    inner sv@(A.SubscriptedVariable m sub v)
      = case sub of
          A.Subscript _ subCheck _
            -> do (es, iv, _) <- collectSubs sv
                  Pointer ct <- details iv
                  let check = if checkValid then subCheck else A.NoCheck
                  -- Arrays should be pointers to the inner element:
                  return (do tell ["("]
                             cgenVariableWithAM checkValid iv A.Original id
                             tell [")"]
                             call genArraySubscript check iv (map (\e -> (findMeta e, call genExpression e)) es)
                         , ct)
          A.SubscriptField _ fieldName
            -> do vt <- astTypeOf v
                  fs <- recordFields m vt
                  ct <- case lookup fieldName fs of
                          Just x -> call getCType m x A.Original
                          Nothing -> dieP m $ "Could not find type of field name: " ++ show fieldName
                  case vt of
                    A.Record {} ->
                      -- For records, we expect it to be a pointer to a record:
                      return
                         (do tell ["("]
                             call genVariable' v A.Original stripPointers
                             tell [")."]
                             genName fieldName
                         , ct)
                    A.ChanDataType {} ->
                      return
                         (do tell ["(&("]
                             call genVariable' v A.Original (const $ Plain "mt_cb_t")
                             let ind = findIndex ((== fieldName) . fst) fs
                             tell [".channels[", maybe "" show ind, "]))"]
                         , ct)
          A.SubscriptFromFor m' subCheck start count
            -> do ct <- details v
                  return (do let check = if checkValid then subCheck else A.NoCheck
                             tell ["(&("]
                             cgenVariableWithAM checkValid v A.Original id
                             call genArraySubscript A.NoCheck v [(m',
                               case check of
                                  A.NoCheck -> call genExpression start
                                  _ -> do tell ["occam_check_slice("]
                                          call genExpression start
                                          genComma
                                          call genExpression count
                                          genComma
                                          call genVariable (specificDimSize 0 v)
                                            A.Original
                                          genComma
                                          genMeta m'
                                          tell [")"]
                               )]
                             tell ["))"]
                         , ct)
    -- | Collect all the plain subscripts on a variable, so we can combine them.
    collectSubs :: A.Variable -> CGen ([A.Expression], A.Variable, A.Type)
    collectSubs (A.SubscriptedVariable m (A.Subscript _ _ e) v)
        = do (es', v', t') <- collectSubs v
             t <- trivialSubscriptType m t'
             return (es' ++ [e], v', t)
    collectSubs v = do t <- astTypeOf v
                       return ([], v, t)

unwrapMobileType :: A.Type -> CGen (Bool, A.Type)
unwrapMobileType (A.Mobile t) = return (True, t)
unwrapMobileType t@(A.Record n)
  = do isMobile <- recordAttr (A.nameMeta n) t >>* A.mobileRecord
       return (isMobile, t)
unwrapMobileType t = return (False, t)

cgetCType :: Meta -> A.Type -> A.AbbrevMode -> CGen CType
cgetCType m origT am
  = do (isMobile, t) <- unwrapMobileType origT
       sc <- fget getScalarType >>* ($ t)
       case (t, sc, isMobile, am) of
         -- Channel arrays are a special case, because they are arrays of pointers
         -- to channels (so that an abbreviated array of channels, and an array
         -- of abbreviations of channels, both look the same)
         (A.Array _ t@(A.Chan {}), _, False, _)
           -> call getCType m t A.Original >>* (Pointer . Pointer)
         (A.Array _ t@(A.ChanEnd {}), _, False, _)
           -> call getCType m t A.Original >>* Pointer
       
         -- All abbrev modes:
         (A.Array _ t, _, False, _)
           -> call getCType m t A.Original >>* (Pointer . const)
         (A.Array {}, _, True, A.Abbrev) -> return $ Pointer $ Pointer $ Plain "mt_array_t"
         (A.Array {}, _, True, _) -> return $ Pointer $ Plain "mt_array_t"

         (A.Record n, _, False, A.Original) -> return $ Plain $ nameString n
         -- Abbrev and ValAbbrev, and mobile:
         (A.Record n, _, False, _) -> return $ Const . Pointer $ const $ Plain $ nameString n
         (A.Record n, _, True, A.Abbrev) -> return $ Pointer $ Pointer $ Plain $ nameString n
         (A.Record n, _, True, _) -> return $ Pointer $ const $ Plain $ nameString n

         (A.Chan (A.ChanAttributes A.Shared A.Shared) _, _, False, _)
           -> return $ Pointer $ Plain "mt_cb_t"
         (A.ChanEnd _ A.Shared _, _, False, _) -> return $ Pointer $ Plain "mt_cb_t"

         (A.Chan {}, _, False, A.Original) -> return $ Plain "Channel"
         (A.Chan {}, _, False, _) -> return $ Pointer $ Plain "Channel"
         (A.ChanEnd {}, _, False, _) -> return $ Pointer $ Plain "Channel"

         (A.ChanDataType {}, _, _, _) -> return $ Pointer $ Plain "mt_cb_t"

         -- Scalar types:
         (_, Just pl, False, A.Original) -> return $ Plain pl
         (_, Just pl, False, A.Abbrev) -> return $ Const $ Pointer $ Plain pl
         (_, Just pl, False, A.ValAbbrev) -> return $ Const $ Plain pl

         -- Mobile scalar types:
         (_, Just pl, True, A.Original) -> return $ Pointer $ Plain pl
         (_, Just pl, True, A.Abbrev) -> return $ Pointer $ Pointer $ Plain pl
         (_, Just pl, True, A.ValAbbrev) -> return $ Pointer $ Const $ Plain pl

         -- This shouldn't happen, but no harm:
         (A.UserDataType {}, _, _, _) -> do t' <- resolveUserType m t
                                            cgetCType m t' am

         -- Must have missed one:
         (_,_,_,am) -> diePC m $ formatCode ("Cannot work out the C type for: % ("
                           ++ show (origT, am) ++ ")") origT
  where
    const = if am == A.ValAbbrev then Const else id

cgenDirectedVariable :: Meta -> A.Type -> CGen () -> A.Direction -> CGen ()
cgenDirectedVariable _ _ var _ = var

genDynamicDim :: A.Variable -> Int -> CGen ()
genDynamicDim v i
  = do A.Array ds _ <- astTypeOf v
       case ds !! i of
         A.Dimension e -> call genExpression e
         A.UnknownDimension ->
           call genVariable (A.SubscriptedVariable m
             (A.Subscript m A.NoCheck $ makeConstant m i)
               $ A.VariableSizes m v) A.Original
      where
        m = findMeta v


cgenArraySubscript :: A.SubscriptCheck -> A.Variable -> [(Meta, CGen ())] -> CGen ()
cgenArraySubscript check v es
    =  do t <- astTypeOf v
          let numDims = case t of
                 A.Array ds _ -> length ds
                 A.Mobile (A.Array ds _) -> length ds
          tell ["["]
          sequence_ $ intersperse (tell ["+"]) $ genPlainSub (genDynamicDim v) es [0..(numDims - 1)]
          tell ["]"]
  where
    -- | Generate the individual offsets that need adding together to find the
    -- right place in the array.
    -- FIXME This is obviously not the best way to factor this, but I figure a
    -- smart C compiler should be able to work it out...
    genPlainSub :: (Int -> CGen ()) -> [(Meta, CGen ())] -> [Int] -> [CGen ()]
    genPlainSub _ [] _ = []
    genPlainSub genDim ((m,e):es) (sub:subs)
        = gen : genPlainSub genDim es subs
      where
        gen = sequence_ $ intersperse (tell ["*"]) $ genSub : genChunks
        genSub
            = case check of
                A.NoCheck -> e
                A.CheckBoth ->
                     do tell ["occam_check_index("]
                        e
                        tell [","]
                        genDim sub
                        tell [","]
                        genMeta m
                        tell [")"]
                A.CheckUpper ->
                     do tell ["occam_check_index_upper("]
                        e
                        tell [","]
                        genDim sub
                        tell [","]
                        genMeta m
                        tell [")"]
                A.CheckLower ->
                     do tell ["occam_check_index_lower("]
                        e
                        tell [","]
                        genMeta m
                        tell [")"]
        genChunks = map genDim subs
--}}}

--{{{  expressions
cgenExpression :: A.Expression -> CGen ()
cgenExpression (A.Monadic m op e) = call genMonadic m op e
cgenExpression (A.Dyadic m op e f) = call genDyadic m op e f
cgenExpression (A.MostPos m t) = call genTypeSymbol "mostpos" t
cgenExpression (A.MostNeg m t) = call genTypeSymbol "mostneg" t
--cgenExpression (A.SizeType m t)
cgenExpression (A.SizeExpr m (A.ExprVariable _ v))
  = do call genVariable (specificDimSize 0 v) A.Original
cgenExpression (A.Conversion m cm t e) = call genConversion m cm t e
cgenExpression (A.ExprVariable m v) = call genVariable v A.Original
cgenExpression (A.Literal _ t lr) = call genLiteral lr t
cgenExpression (A.True m) = tell ["true"]
cgenExpression (A.False m) = tell ["false"]
--cgenExpression (A.FunctionCall m n es)
cgenExpression (A.IntrinsicFunctionCall m s es) = call genIntrinsicFunction m s es
--cgenExpression (A.BytesInExpr m e)
cgenExpression (A.BytesInExpr m (A.ExprVariable _ v))
  = do t <- astTypeOf v
       call genBytesIn m t (Right v)
cgenExpression (A.BytesInType m t) = call genBytesIn m t (Left False)
--cgenExpression (A.OffsetOf m t n)
--cgenExpression (A.ExprConstr {})
cgenExpression (A.AllocMobile m t me) = call genAllocMobile m t me
cgenExpression (A.CloneMobile m e) = call genCloneMobile m e
cgenExpression (A.IsDefined m (A.ExprVariable _ (A.DerefVariable _ v)))
  = tell ["("] >> call genVariable v A.Original >> tell ["!=NULL)"]
cgenExpression (A.IsDefined m e)
  = tell ["("] >> call genExpression e >> tell ["!=NULL)"]
cgenExpression t = call genMissing $ "genExpression " ++ show t

cgenTypeSymbol :: String -> A.Type -> CGen ()
cgenTypeSymbol s t
 = do f <- fget getScalarType
      case (t, f t) of
        (A.Time, _) -> tell ["occam_", s, "_time"]
        (_, Just ct) -> tell ["occam_", s, "_", ct]
        (_, Nothing) -> call genMissingC $ formatCode "genTypeSymbol %" t

cgenIntrinsicFunction :: Meta -> String -> [A.Expression] -> CGen ()
cgenIntrinsicFunction m s es
    =  do let (funcName, giveMeta) = case lookup s simpleFloatIntrinsics of
                  Just (_,cName) -> (cName, False)
                  Nothing -> ("occam_" ++ [if c == '.' then '_' else c | c <- s], True)
          tell [funcName, "("]
          seqComma [call genExpression e | e <- es]
          when (giveMeta) $ genComma >> genMeta m
          tell [")"]
--}}}

--{{{  operators
cgenSimpleMonadic :: String -> A.Expression -> CGen ()
cgenSimpleMonadic s e
    =  do tell ["(", s]
          call genExpression e
          tell [")"]

cgenFuncMonadic :: Meta -> String -> A.Expression -> CGen ()
cgenFuncMonadic m s e
    =  do t <- astTypeOf e
          call genTypeSymbol s t
          tell [" ("]
          call genExpression e
          tell [", "]
          genMeta m
          tell [")"]

cgenMonadic :: Meta -> A.MonadicOp -> A.Expression -> CGen ()
cgenMonadic m A.MonadicSubtr e = call genFuncMonadic m "negate" e
cgenMonadic _ A.MonadicMinus e = call genSimpleMonadic "-" e
cgenMonadic _ A.MonadicBitNot e = call genSimpleMonadic "~" e
cgenMonadic _ A.MonadicNot e = call genSimpleMonadic "!" e

cgenSimpleDyadic :: String -> A.Expression -> A.Expression -> CGen ()
cgenSimpleDyadic s e f
    =  do tell ["("]
          call genExpression e
          tell [" ", s, " "]
          call genExpression f
          tell [")"]

cgenFuncDyadic :: Meta -> String -> A.Expression -> A.Expression -> CGen ()
cgenFuncDyadic m s e f
    =  do t <- astTypeOf e
          call genTypeSymbol s t
          tell [" ("]
          call genExpression e
          tell [", "]
          call genExpression f
          tell [", "]
          genMeta m
          tell [")"]

cgenDyadic :: Meta -> A.DyadicOp -> A.Expression -> A.Expression -> CGen ()
cgenDyadic m A.Add e f = call genFuncDyadic m "add" e f
cgenDyadic m A.Subtr e f = call genFuncDyadic m "subtr" e f
cgenDyadic m A.Mul e f = call genFuncDyadic m "mul" e f
cgenDyadic m A.Div e f = call genFuncDyadic m "div" e f
cgenDyadic m A.Rem e f = call genFuncDyadic m "rem" e f
cgenDyadic m A.Plus e f = call genFuncDyadic m "plus" e f
cgenDyadic m A.Minus e f = call genFuncDyadic m "minus" e f
cgenDyadic m A.Times e f = call genFuncDyadic m "times" e f
cgenDyadic m A.LeftShift e f = call genFuncDyadic m "lshift" e f
cgenDyadic m A.RightShift e f = call genFuncDyadic m "rshift" e f
cgenDyadic _ A.BitAnd e f = call genSimpleDyadic "&" e f
cgenDyadic _ A.BitOr e f = call genSimpleDyadic "|" e f
cgenDyadic _ A.BitXor e f = call genSimpleDyadic "^" e f
cgenDyadic _ A.And e f = call genSimpleDyadic "&&" e f
cgenDyadic _ A.Or e f = call genSimpleDyadic "||" e f
cgenDyadic _ A.Eq e f = call genSimpleDyadic "==" e f
cgenDyadic _ A.NotEq e f = call genSimpleDyadic "!=" e f
cgenDyadic _ A.Less e f = call genSimpleDyadic "<" e f
cgenDyadic _ A.More e f = call genSimpleDyadic ">" e f
cgenDyadic _ A.LessEq e f = call genSimpleDyadic "<=" e f
cgenDyadic _ A.MoreEq e f = call genSimpleDyadic ">=" e f
cgenDyadic _ A.Concat e f = call genListConcat e f
--}}}

cgenListConcat :: A.Expression -> A.Expression -> CGen ()
cgenListConcat a b
  = do tell ["tock_queue_concat("]
       call genExpression a
       tell [","]
       call genExpression b
       tell [")"]

--{{{  input/output items

genChan, genDest :: A.Variable -> CGen ()
genDest v = call genVariable' v A.Original (Pointer . stripPointers)
genChan c = call genVariable' c A.Original (const $ Pointer $ Plain "Channel")
 
cgenInputItem :: A.Variable -> A.InputItem -> CGen ()
cgenInputItem c (A.InCounted m cv av)
    =  do call genInputItem c (A.InVariable m cv)
          t <- astTypeOf av
          tell ["ChanIn(wptr,"]
          genChan c
          tell [","]
          genDest av
          tell [","]
          subT <- trivialSubscriptType m t
          call genVariable cv A.Original
          tell ["*"]
          call genBytesIn m subT (Right av)
          tell [");"]
cgenInputItem c (A.InVariable m v)
    =  do case v of
            -- If we are reading into a dereferenced mobile, we must make sure
            -- that something is in that mobile first:
            A.DerefVariable _ v' -> do
                 tell ["if ("]
                 call genVariable v' A.Original
                 tell ["==NULL){"]
                 call genVariable v' A.Original
                 tell ["="]
                 t <- astTypeOf v'
                 call genAllocMobile m t Nothing
                 tell [";}"]
            _ -> return ()
          t <- astTypeOf v
          isMobile <- isMobileType t
          let rhs = genDest v
          case (t, isMobile) of
            (A.Int, _) ->
              do tell ["ChanInInt(wptr,"]
                 genChan c
                 tell [","]
                 rhs
                 tell [");"]
            (_, True) ->
              do call genClearMobile m v -- TODO insert this via a pass
                 tell ["MTChanIn(wptr,"]
                 genChan c
                 tell [",(void**)"]
                 rhs
                 tell [");"]
            _ ->
              do tell ["ChanIn(wptr,"]
                 genChan c
                 tell [","]
                 rhs
                 tell [","]
                 call genBytesIn m t (Right v)
                 tell [");"]

cgenOutputItem :: A.Type -> A.Variable -> A.OutputItem -> CGen ()
cgenOutputItem _ c (A.OutCounted m ce ae)
    =  do tce <- astTypeOf ce
          call genOutputItem tce c (A.OutExpression m ce)
          t <- astTypeOf ae
          case ae of
            A.ExprVariable m v ->
              do tell ["ChanOut(wptr,"]
                 genChan c
                 tell [","]
                 call genVariable v A.Abbrev
                 tell [","]
                 subT <- trivialSubscriptType m t
                 call genExpression ce
                 tell ["*"]
                 call genBytesIn m subT (Right v)
                 tell [");"]
cgenOutputItem innerT c (A.OutExpression m e)
    = do isMobile <- isMobileType innerT
         case (innerT, isMobile, e) of
            (A.Int, _, _) ->
              do tell ["ChanOutInt(wptr,"]
                 genChan c
                 tell [","]
                 call genExpression e
                 tell [");"]
            (_, True, A.ExprVariable _ v) ->
              do tell ["MTChanOut(wptr,"]
                 genChan c
                 tell [",(void*)"]
                 call genVariable' v A.Original Pointer
                 tell [");"]
            (_, _, A.ExprVariable _ v) ->
              do tell ["ChanOut(wptr,"]
                 genChan c
                 tell [","]
                 call genVariable v A.Abbrev
                 tell [","]
                 te <- astTypeOf e
                 call genBytesIn m te (Right v)
                 tell [");"]
--}}}

--{{{  replicators
cgenReplicatorStart :: A.Name -> A.Replicator -> CGen ()
cgenReplicatorStart n rep
    =  do tell ["for("]
          call genReplicatorLoop n rep
          tell ["){"]
cgenReplicatorEnd :: A.Replicator -> CGen ()
cgenReplicatorEnd rep = tell ["}"]

cgenReplicatorLoop :: A.Name -> A.Replicator -> CGen ()
cgenReplicatorLoop index (A.For m base count step)
  -- It is now too hard to work out statically if we could make this a
  -- simple loop (without an additional counter), because step may be
  -- negative (and that may be determined at run-time.  So we will generate the
  -- most general loop, and let the C compiler optimise if possibe:
    =      do counter <- csmLift $ makeNonce m "replicator_count"
              tell ["int ", counter, "="]
              call genExpression count
              tell [","]
              genName index
              tell ["="]
              call genExpression base
              tell [";", counter, ">0;", counter, "--,"]
              genName index
              tell ["+="]
              call genExpression step
cgenReplicatorLoop _ _ = cgenMissing "ForEach loops not yet supported in the C backend"
--}}}

--{{{  abbreviations

-- | Generate the size part of a RETYPES\/RESHAPES abbrevation of a variable.
cgenRetypeSizes :: Meta -> A.Type -> A.Name -> A.Type -> A.Variable -> CGen ()
cgenRetypeSizes _ (A.Chan {}) _ (A.Chan {}) _ = return ()
cgenRetypeSizes _ (A.ChanEnd {}) _ (A.ChanEnd {}) _ = return ()
cgenRetypeSizes m destT destN srcT srcV
    =     let size = do tell ["occam_check_retype("]
                        call genBytesIn m srcT (Right srcV)
                        tell [","]
                        call genBytesIn m destT (Left True)
                        tell [","]
                        genMeta m
                        tell [")"]
              isVarArray = case destT of
                A.Array ds _ -> A.UnknownDimension `elem` ds
                _ -> False in
          if isVarArray
            then size >> tell [";"]
            else
              do tell ["if("]
                 size
                 tell ["!=1){"]
                 call genStop m "size mismatch in RETYPES"
                 tell ["}"]

-- | Generate the right-hand side of an abbreviation of an expression.
abbrevExpression :: A.AbbrevMode -> A.Type -> A.Expression -> CGen ()
abbrevExpression am t@(A.Array _ _) e
    = case e of
        A.ExprVariable _ v -> call genVariable v am
        A.Literal _ t@(A.Array _ _) r -> call genExpression e
        _ -> call genMissingC $ formatCode "array expression abbreviation %" e
abbrevExpression am t@(A.Record _) (A.ExprVariable _ v)
    = call genVariable v am
abbrevExpression am _ e = call genExpression e
--}}}

--{{{  specifications
cgenSpec :: Level -> A.Specification -> CGen b -> CGen b
cgenSpec lvl spec body
    =  do call introduceSpec lvl spec
          x <- body
          call removeSpec spec
          return x

-- | Generate a declaration of a new variable.
cgenDeclaration :: Level -> A.Type -> A.Name -> Bool -> CGen ()
cgenDeclaration lvl at@(A.Array ds t) n False
    =  do genStatic lvl n
          genType t
          tell [" "]
          case t of
            A.Chan _ _ ->
              do genName n
                 tell ["_storage"]
                 call genFlatArraySize ds
                 tell [";"]
                 genType t
                 tell ["* "]
            _ -> return ()
          call genArrayStoreName n
          call genFlatArraySize ds
          tell [";"]
cgenDeclaration lvl (A.Array ds t) n True
    =  do genStatic lvl n
          genType t
          tell [" "]
          call genArrayStoreName n
          call genFlatArraySize ds
          tell [";"]
cgenDeclaration lvl t n _
    =  do genStatic lvl n
          genType t
          tell [" "]
          genName n
          tell [";"]

-- | Generate the size of the C array that an occam array of the given
-- dimensions maps to.
cgenFlatArraySize :: [A.Dimension] -> CGen ()
cgenFlatArraySize ds
    =  do tell ["["]
          sequence $ intersperse (tell ["*"])
                                 [call genExpression n | A.Dimension n <- ds]
          tell ["]"]
-- FIXME: genBytesInArrayDim could share with this

-- | Initialise an item being declared.
cdeclareInit :: Meta -> A.Type -> A.Variable -> Maybe (CGen ())
cdeclareInit _ (A.Chan (A.ChanAttributes A.Unshared A.Unshared) _) var
    = Just $ do tell ["ChanInit(wptr,"]
                call genVariableUnchecked var A.Abbrev
                tell [");"]
cdeclareInit _ (A.Chan (A.ChanAttributes A.Shared A.Shared) _) var
    = Just $ do call genVariable' var A.Original (const $ Pointer $ Plain "mt_cb_t")
                tell [" = MTAllocChanType(wptr, 1, true);"]
cdeclareInit m t@(A.Array ds t') var
    = Just $ do case t' of
                  A.Chan _ _ ->
                    do tell ["tock_init_chan_array("]
                       call genVariableUnchecked var A.Original
                       tell ["_storage,"]
                       call genVariableUnchecked var A.Original
                       tell [","]
                       sequence_ $ intersperse (tell ["*"])
                                   [call genExpression n | A.Dimension n <- ds]
                       -- FIXME: and again
                       tell [");"]
                  _ -> return ()
                fdeclareInit <- fget declareInit
                init <- return (\sub -> fdeclareInit m t' (sub var))
                call genOverArray m var init
cdeclareInit m rt@(A.Record _) var
    = Just $ do fs <- recordFields m rt
                sequence_ [initField t (A.SubscriptedVariable m (A.SubscriptField m n) var)
                           | (n, t) <- fs]
                isMobile <- recordAttr m rt >>* A.mobileRecord
                when isMobile $ do
                  call genVariableUnchecked var A.Original
                  tell ["=NULL;"]
                  call genAssign m [var] $ A.ExpressionList m [A.AllocMobile m rt Nothing]
  where
    initField :: A.Type -> A.Variable -> CGen ()
    initField t v = do fdeclareInit <- fget declareInit
                       doMaybe $ fdeclareInit m t v
cdeclareInit m t@(A.Mobile t') var
  = Just $ do call genVariableUnchecked var A.Original
              tell ["=NULL;"]
              case t' of
                A.Array ds _ | A.UnknownDimension `elem` ds -> return ()
                _ -> call genAssign m [var] $ A.ExpressionList m [A.AllocMobile m t Nothing]
cdeclareInit m (A.ChanDataType {}) var
  = Just $ do call genVariable' var A.Original (const $ Pointer $ Plain "mt_cb_t")
              tell ["=NULL;"]
cdeclareInit _ _ _ = Nothing

-- | Free a declared item that's going out of scope.
cdeclareFree :: Meta -> A.Type -> A.Variable -> Maybe (CGen ())
cdeclareFree m (A.Mobile {}) v = Just $ call genClearMobile m v
cdeclareFree _ _ _ = Nothing

{-
                  Original        Abbrev
INT x IS y:       int *x = &y;    int *x = &(*y);
[]INT xs IS ys:   int *xs = ys;   int *xs = ys;
                  const int xs_sizes[] = ys_sizes;

CHAN OF INT c IS d:       Channel *c = d;

[10]CHAN OF INT cs:       Channel tmp[10];
                          Channel *cs[10];
                          for (...) { cs[i] = &tmp[i]; ChanInit(cs[i]); }
                          const int cs_sizes[] = { 10 };
[]CHAN OF INT ds IS cs:   Channel **ds = cs;
                          const int *ds_sizes = cs_sizes;
-}
cintroduceSpec :: Level -> A.Specification -> CGen ()
cintroduceSpec lvl (A.Specification m n (A.Declaration _ t))
    = do call genDeclaration lvl t n False
         fdeclareInit <- fget declareInit
         case fdeclareInit m t (A.Variable m n) of
           Just p -> p
           Nothing -> return ()
cintroduceSpec lvl (A.Specification _ n (A.Is _ am t (A.ActualVariable v)))
    =  do let rhs = call genVariable v am
          call genDecl lvl am t n
          tell ["="]
          rhs
          tell [";"]
cintroduceSpec lvl (A.Specification m n (A.Is _ am t (A.ActualExpression e)))
    =  do let rhs = abbrevExpression am t e
          case (am, t, e) of
            (A.ValAbbrev, A.Array _ ts, A.Literal _ _ _) ->
              -- For "VAL []T a IS [vs]:", we have to use [] rather than * in the
              -- declaration, since you can't say "int *foo = {vs};" in C.
              do genStatic lvl n
                 tell ["const "]
                 genType ts
                 tell [" "]
                 genName n
                 tell ["[] = "]
                 rhs
                 tell [";\n"]
            (A.ValAbbrev, A.Record _, A.Literal _ _ _) ->
              -- Record literals are even trickier, because there's no way of
              -- directly writing a struct literal in C that you can use -> on.
              do tmp <- csmLift $ makeNonce m "record_literal"
                 genStatic lvl n
                 tell ["const "]
                 genType t
                 tell [" ", tmp, " = "]
                 rhs
                 tell [";\n"]
                 call genDecl lvl am t n
                 tell [" = &", tmp, ";\n"]
            _ ->
              do call genDecl lvl am t n
                 tell [" = "]
                 rhs
                 tell [";\n"]
cintroduceSpec lvl (A.Specification _ n (A.Is _ _ (A.Array _ c) (A.ActualChannelArray cs)))
    =  do genStatic lvl n
          genType c
          case c of
             A.Chan _ _ -> tell ["* "]
             -- Channel ends don't need an extra indirection; in C++ they are not
             -- pointers, and in C they are already pointers
             _ -> tell [" "]
          call genArrayStoreName n
          tell ["[]={"]
          seqComma (map (\v -> call genVariable v A.Abbrev) cs)
          tell ["};"]
cintroduceSpec lvl (A.Specification _ n (A.Is _ _ _ (A.ActualClaim v)))
    =  do t <- astTypeOf n
          case t of
            A.ChanEnd dir _ _ -> do call genDecl lvl A.Original t n
                                    tell ["=(&(((mt_cb_t*)"]
                                    lock dir
                                    tell [")->channels[0]));"]
            A.ChanDataType dir _ _ -> do call genDecl lvl A.Original t n
                                         tell ["="]
                                         lock dir
                                         tell [";"]
  where
    lock dir = do tell ["TockMTLock(wptr,"]
                  call genVariable' v A.Original (const $ Pointer $ Plain "mt_cb_t")
                  tell [",",if dir == A.DirInput
                              then "MT_CB_CLIENT"
                              else "MT_CB_SERVER"
                       ,")"]
cintroduceSpec _ (A.Specification _ _ (A.DataType _ _)) = return ()
cintroduceSpec _ (A.Specification _ _ (A.RecordType _ _ _)) = return ()
cintroduceSpec _ (A.Specification _ _ (A.ChanBundleType {})) = return ()
cintroduceSpec _ (A.Specification _ n (A.Protocol _ _)) = return ()
cintroduceSpec _ (A.Specification _ n (A.ProtocolCase _ ts))
    =  do tell ["typedef enum{"]
          seqComma [genName tag >> tell ["_"] >> genName n | (tag, _) <- ts]
          -- You aren't allowed to have an empty enum.
          when (ts == []) $
            tell ["empty_protocol_"] >> genName n
          tell ["}"]
          genName n
          tell [";"]
cintroduceSpec lvl (A.Specification _ n st@(A.Proc _ _ _ _))
    = genProcSpec lvl n st False
cintroduceSpec lvl (A.Specification _ n (A.Retypes m am t v))
    =  do origT <- astTypeOf v
          let rhs = call genVariable v A.Abbrev
          call genDecl lvl am t n
          tell ["="]
          -- For scalar types that are VAL abbreviations (e.g. VAL INT64),
          -- we need to dereference the pointer that abbrevVariable gives us.
          let deref = case (am, t) of
                        (_, A.Array _ _) -> False
                        (_, A.Chan {}) -> False
                        (_, A.ChanEnd {}) -> False
                        (_, A.Record {}) -> False
                        (A.ValAbbrev, _) -> True
                        _ -> False
          when deref $ tell ["*"]
          tell ["("]
          genCType m t am
          when deref $ tell ["*"]
          tell [")"]
          rhs
          tell [";"]
          call genRetypeSizes m t n origT v
cintroduceSpec _ (A.Specification _ n (A.Rep m rep))
   = call genReplicatorStart n rep
--cintroduceSpec (A.Specification _ n (A.RetypesExpr _ am t e))
cintroduceSpec _ n = call genMissing $ "introduceSpec " ++ show n

cgenRecordTypeSpec :: A.Name -> A.RecordAttr -> [(A.Name, A.Type)] -> CGen ()
cgenRecordTypeSpec n attr fs
    =  do tell ["typedef struct{"]
          sequence_ [call genDeclaration NotTopLevel t n True | (n, t) <- fs]
          tell ["}"]
          when (A.packedRecord attr || A.mobileRecord attr) $ tell [" occam_struct_packed "]
          genName n
          tell [";"]
          if null [t | (_, A.Mobile t) <- fs]
            then do genStatic TopLevel n
                    tell ["const word "]
                    genName n
                    tell ["_mttype = MT_SIMPLE | MT_MAKE_TYPE(MT_DATA);"]
                    genStatic TopLevel n
                    tell ["const int "]
                    genName n
                    tell ["_mtsize = sizeof("]
                    genName n
                    tell [");"]
                    -- Not quite certain CCSP handles these descriptors:
            else do genStatic TopLevel n
                    tell ["const word "]
                    genName n
                    tell ["_mttype[", show (length mtEntries), "] = {"]
                    seqComma mtEntries
                    tell ["};"]
                    genStatic TopLevel n
                    tell ["const int "]
                    genName n
                    tell ["_mtsize = ", show (length mtEntries), ";"]
  where
    mtEntries :: [CGen ()]
    mtEntries = concatMap (mt . snd) fs

    mt :: A.Type -> [CGen ()]
    mt (A.Array ds t)
      = [do tell ["MT_FARRAY|MT_FARRAY_LEN("]
            sequence_ $ intersperse (tell ["*"]) [call genExpression e
                                                 | A.Dimension e <- ds]
            tell [")"]
        ] ++ mt t
    mt t = [mobileElemType False t]

cgenForwardDeclaration :: A.Specification -> CGen ()
cgenForwardDeclaration (A.Specification _ n st@(A.Proc _ _ _ _))
    = genProcSpec TopLevel n st True
cgenForwardDeclaration (A.Specification _ n (A.RecordType _ b fs))
    = call genRecordTypeSpec n b fs
cgenForwardDeclaration _ = return ()

cremoveSpec :: A.Specification -> CGen ()
cremoveSpec (A.Specification m n (A.Declaration _ t))
 = do fdeclareFree <- fget declareFree
      case fdeclareFree m t var of
        Just p -> p
        Nothing -> return ()
  where
    var = A.Variable m n
cremoveSpec (A.Specification _ n (A.Rep _ rep))
  = call genReplicatorEnd rep
cremoveSpec (A.Specification m n (A.Is _ am t (A.ActualExpression e)))
  = do fdeclareFree <- fget declareFree
       case fdeclareFree m t var of
         Just p -> p
         Nothing -> return ()
  where
    var = A.Variable m n
cremoveSpec (A.Specification _ n (A.Is _ _ _ (A.ActualClaim v)))
    =  do t <- astTypeOf n
          let dir = case t of
                      A.ChanEnd dir _ _ -> dir
                      A.ChanDataType dir _ _ -> dir
          tell ["MTUnlock(wptr,"]
          call genVariable' v A.Original (const $ Pointer $ Plain "mt_cb_t")
          tell [",",if dir == A.DirInput
                      then "MT_CB_CLIENT"
                      else "MT_CB_SERVER"
               ,");"]

cremoveSpec _ = return ()

cgenSpecMode :: A.SpecMode -> CGen ()
cgenSpecMode A.PlainSpec = return ()
cgenSpecMode A.InlineSpec = tell ["inline "]
--}}}

--{{{  formals, actuals, and calling conventions
prefixComma :: [CGen ()] -> CGen ()
prefixComma cs = sequence_ [genComma >> c | c <- cs]

cgenActuals :: [A.Formal] -> [A.Actual] -> CGen ()
cgenActuals fs as
  = do when (length fs /= length as) $
         dieP (findMeta (fs, as)) $ "Mismatch in numbers of parameters in backend: "
           ++ show (length fs) ++ " expected, but actually: " ++ show (length as)
       seqComma [call genActual f a | (f, a) <- zip fs as]

cgenActual :: A.Formal -> A.Actual -> CGen ()
cgenActual f a = seqComma $ realActuals f a id

-- | Return generators for all the real actuals corresponding to a single
-- actual.
realActuals :: A.Formal -> A.Actual -> (CType -> CType) -> [CGen ()]
realActuals (A.Formal am _ _) (A.ActualExpression (A.ExprVariable _ v)) fct
    = [call genVariable' v am fct]
realActuals _ (A.ActualExpression e) _
    = [call genExpression e]
realActuals (A.Formal am _ _) (A.ActualVariable v) fct
    = [call genVariable' v am fct]

-- | Return (type, name) generator pairs for all the real formals corresponding
-- to a single formal.
realFormals :: A.Formal -> [(CGen (), CGen ())]
realFormals (A.Formal am t n)
    = [(genCType (A.nameMeta n) t am, genName n)]

-- | Generate a Proc specification, which maps to a C function.
-- This will use ProcGetParam if the Proc is in csParProcs, or the normal C
-- calling convention otherwise.  If will not munge the name if the process was
-- one of the original top-level procs, other than to add an occam_ prefix (which
-- avoids name collisions).
genProcSpec :: Level -> A.Name -> A.SpecType -> Bool -> CGen ()
genProcSpec lvl n (A.Proc _ (sm, rm) fs p) forwardDecl
    =  do cs <- getCompState
          let (header, params) = if n `Set.member` csParProcs cs
                                    || rm == A.Recursive
                                   then (genParHeader, genParParams)
                                   else (genNormalHeader, return ())
          genStatic lvl n
          header
          if forwardDecl
            then tell [";\n"]
            else do tell ["{\n"]
                    params
                    call genProcess p
                    tell ["}\n"]
  where
    rfs = concatMap realFormals fs

    genParHeader :: CGen ()
    genParHeader
        =  do -- These can't be inlined, since they're only used as function
              -- pointers.
              tell ["void "]
              genName n
              tell [" (Workspace wptr)"]

    genParParams :: CGen ()
    genParParams
        = sequence_ [do t
                        tell [" "]
                        n
                        tell [" = ProcGetParam (wptr, " ++ show num ++ ", "]
                        t
                        tell [");\n"]
                     | (num, (t, n)) <- zip [(0 :: Int) ..] rfs]

    genNormalHeader :: CGen ()
    genNormalHeader
        =  do call genSpecMode sm
              tell ["void "]
              genName n
              tell [" (Workspace wptr"]
              sequence_ [do tell [", "]
                            t
                            tell [" "]
                            n
                         | (t, n) <- rfs]
              tell [")"]

-- | Generate a ProcAlloc for a PAR subprocess, returning a nonce for the
-- workspace pointer and the name of the function to call.
cgenProcAlloc :: A.Name -> [A.Formal] -> [A.Actual] -> CGen (String, CGen ())
cgenProcAlloc n fs as
    =  do ras <- liftM concat $ sequence
                [do isMobile <- isMobileType t
                    let (s, fct) = case (am, isMobile) of
                              (A.ValAbbrev, _) -> ("ProcParam", id)
                              -- This is not needed unless forking:
                              --(_, True) -> ("ProcMTMove", Pointer)
                              _ -> ("ProcParam", id)
                    return $ zip (repeat s) $ realActuals f a fct
                | (f@(A.Formal am t _), a) <- zip fs as]

          ws <- csmLift $ makeNonce (A.nameMeta n) "workspace"
          tell ["Workspace ", ws, " = TockProcAlloc (wptr, ", show $ length ras, ", "]
          genName n
          tell ["_stack_size);\n"]

          sequence_ [do tell [pc, " (wptr, ", ws, ", ", show num, ", "]
                        ra
                        tell [");\n"]
                     | (num, (pc, ra)) <- zip [(0 :: Int)..] ras]

          return (ws, genName n)
--}}}

--{{{  processes
cgenProcess :: A.Process -> CGen ()
cgenProcess p = case p of
  A.Assign m vs es -> call genAssign m vs es
  A.Input m c im -> call genInput c im
  A.Output m c ois ->
    do Left ts <- protocolItems c
       call genOutput c $ zip ts ois
  A.OutputCase m c t ois -> call genOutputCase c t ois
  A.Skip m -> tell ["/* skip */\n"]
  A.Stop m -> call genStop m "STOP process"
  A.Seq _ s -> call genSeq s
  A.If m s -> call genIf m s
  A.Case m e s -> call genCase m e s
  A.While m e p -> call genWhile e p
  A.Par m pm s -> call genPar pm s
  -- PROCESSOR does nothing special.
  A.Processor m e p -> call genProcess p
  A.Alt m b s -> call genAlt b s
  A.InjectPoison m ch -> call genPoison m ch
  A.ProcCall m n as -> call genProcCall n as
  A.IntrinsicProcCall m s as -> call genIntrinsicProc m s as

--{{{  assignment
cgenAssign :: Meta -> [A.Variable] -> A.ExpressionList -> CGen ()
cgenAssign m [v] (A.ExpressionList _ [e])
    = do t <- astTypeOf v
         trhs <- astTypeOf e
         f <- fget getScalarType
         isMobile <- isMobileType t
         case f t of
           Just _ -> doAssign v e
           Nothing -> case (t, isMobile, trhs) of
             -- Assignment of channel-ends, but not channels, is possible (at least in Rain):
             (A.ChanEnd A.DirInput _ _, _, _) -> doAssign v e
             (A.ChanEnd A.DirOutput _ _, _, _) -> doAssign v e
             (A.List _, _, _) -> call genListAssign v e
             (A.Mobile (A.List _), _, _) -> call genListAssign v e
             (_, True, _)
               -> do call genClearMobile m v
                     case e of
                       A.AllocMobile _ _ Nothing -> doAssign v e
                       A.AllocMobile m t (Just init)
                         -> do doAssign v $ A.AllocMobile m t Nothing
                               call genAssign m [A.DerefVariable m v]
                                 $ A.ExpressionList m [init]
                       A.CloneMobile {} -> doAssign v e
                       A.ExprVariable _ vrhs ->
                         do doAssign v e
                            call genVariable vrhs A.Original
                            tell ["=NULL;"]
                       _ -> call genMissing $ "Mobile assignment from " ++ show e
             (A.Array ds innerT, _, _) | isPOD innerT && A.UnknownDimension `notElem` ds
               -> do tell ["memcpy("]
                     call genVariable v A.Abbrev
                     tell [","]
                     call genExpression e
                     tell [","]
                     call genBytesIn m t (Left False)
                     tell [");"]
             (_, _, A.Array ds innerT) | isPOD innerT && A.UnknownDimension `notElem` ds
               -> do tell ["memcpy("]
                     call genVariable v A.Abbrev
                     tell [","]
                     call genExpression e
                     tell [","]
                     call genBytesIn m trhs (Left False)
                     tell [");"]
             _ -> call genMissingC $ formatCode "assignment of type %" t
  where
    doAssign :: A.Variable -> A.Expression -> CGen ()
    doAssign v e
        = do call genVariable v A.Original
             tell ["="]
             call genExpression e
             tell [";"]
cgenAssign m (v:vs) (A.IntrinsicFunctionCallList _ n es)
    = do call genVariable v A.Original
         let (funcName, giveMeta) = case lookup n simpleFloatIntrinsics of
                Just (_,cName) -> (cName, False)
                Nothing -> ("occam_" ++ [if c == '.' then '_' else c | c <- n], True)
         tell ["=",funcName,"("]
         seqComma $ map (call genExpression) es
         mapM (\v -> tell [","] >> call genActual (A.Formal A.Abbrev A.Int (A.Name
           emptyMeta "dummy_intrinsic_param")) (A.ActualVariable v)) vs
         when giveMeta $ genComma >> genMeta m
         tell [");"]
cgenAssign m [vA, vB] (A.AllocChannelBundle _ n)
    = do t@(A.ChanDataType dirA shA _) <- astTypeOf vA
         A.ChanDataType dirB shB _ <- astTypeOf vB
         call genClearMobile m vA
         call genClearMobile m vB
         fs <- recordFields m t
         call genVariable' vA A.Original (const $ Pointer $ Plain "mt_cb_t")
         tell ["=MTAllocChanType(wptr,", show (length fs), ",",
           if shA == A.Shared || shB == A.Shared then "true" else "false", ");"]
         -- Mobile channel types start with a reference count of 2, so no need
         -- to clone, just assign:
         call genVariable' vB A.Original (const $ Pointer $ Plain "mt_cb_t")
         tell ["="]
         call genVariable' vA A.Original (const $ Pointer $ Plain "mt_cb_t")
         tell [";"]
  where
    el e = A.ExpressionList m [e]
cgenAssign m _ _ = call genMissing "Cannot perform assignment with multiple destinations or multiple sources"

isPOD :: A.Type -> Bool
isPOD = isJust . cgetScalarType

--}}}
--{{{  input
cgenInput :: A.Variable -> A.InputMode -> CGen ()
cgenInput c im
    =  do case im of
            A.InputTimerRead m (A.InVariable m' v) -> call genTimerRead c v
            A.InputTimerAfter m e -> call genTimerWait e
            A.InputSimple m is -> sequence_ $ map (call genInputItem c) is
            _ -> call genMissing $ "genInput " ++ show im

cgenTimerRead :: A.Variable -> A.Variable -> CGen ()
cgenTimerRead _ v = cgenGetTime v

cgenTimerWait :: A.Expression -> CGen ()
cgenTimerWait e
    =  do tell ["TimerWait(wptr,"]
          call genExpression e
          tell [");"]

cgenGetTime :: A.Variable -> CGen ()
cgenGetTime v
    =  do call genVariable v A.Original
          tell [" = TimerRead(wptr);"]

--}}}
--{{{  output
cgenOutput :: A.Variable -> [(A.Type, A.OutputItem)] -> CGen ()
cgenOutput c tois = sequence_ [call genOutputItem t c oi | (t, oi) <- tois]

cgenOutputCase :: A.Variable -> A.Name -> [A.OutputItem] -> CGen ()
cgenOutputCase c tag ois
    =  do t <- astTypeOf c
          let proto = case t of
                        A.Chan _ (A.UserProtocol n) -> n
                        A.ChanEnd _ _ (A.UserProtocol n) -> n
          tell ["ChanOutInt(wptr,"]
          call genVariable c A.Abbrev
          tell [","]
          genName tag
          tell ["_"]
          genName proto
          tell [");"]
          Right ps <- protocolItems c
          let ts = fromMaybe (error "genOutputCase unknown tag")
                     $ lookup tag ps
          call genOutput c $ zip ts ois
--}}}
--{{{  stop
cgenStop :: Meta -> String -> CGen ()
cgenStop m s
    =  do tell ["occam_stop("]
          genMeta m
          tell [",1,\"", s, "\");"]
--}}}
--{{{  seq
cgenSeq :: A.Structured A.Process -> CGen ()
cgenSeq s = call genStructured NotTopLevel s doP >> return ()
  where
    doP _ p = call genProcess p
--}}}
--{{{  if
cgenIf :: Meta -> A.Structured A.Choice -> CGen ()
cgenIf m s | justOnly s = do call genStructured NotTopLevel s doCplain
                             tell ["{"]
                             call genStop m "no choice matched in IF process"
                             tell ["}"]
           | otherwise
    =  do label <- csmLift $ makeNonce m "if_end"
          tell ["/*",label,"*/"]
          genIfBody label s
          call genStop m "no choice matched in IF process"
          tell [label, ":;"]
  where
    genIfBody :: String -> A.Structured A.Choice -> CGen ()
    genIfBody label s = call genStructured NotTopLevel s doC >> return ()
      where
        doC m (A.Choice m' e p)
            = do tell ["if("]
                 call genExpression e
                 tell ["){"]
                 call genProcess p
                 tell ["goto ", label, ";"]
                 tell ["}"]
    doCplain _ (A.Choice _ e p)
      = do tell ["if("]
           call genExpression e
           tell ["){"]
           call genProcess p
           tell ["}else "]

justOnly :: Data a => A.Structured a -> Bool
justOnly (A.Only {}) = True
justOnly (A.Several _ ss) = all justOnly ss
justOnly _ = False
--}}}
--{{{  case
cgenCase :: Meta -> A.Expression -> A.Structured A.Option -> CGen ()
cgenCase m e s
    =  do tell ["switch("]
          call genExpression e
          tell ["){"]
          seenDefault <- genCaseBody (return ()) s
          when (not seenDefault) $
            do tell ["default:"]
               call genStop m "no option matched in CASE process"
          tell ["}"]
  where
    genCaseBody :: CGen () -> A.Structured A.Option -> CGen Bool
    genCaseBody coll (A.Spec _ spec s)
        = genCaseBody (call genSpec NotTopLevel spec coll) s
    genCaseBody coll (A.Only _ (A.Option _ es p))
        =  do sequence_ [tell ["case "] >> call genExpression e >> tell [":"] | e <- es]
              tell ["{"]
              coll
              call genProcess p
              tell ["}break;"]
              return False
    genCaseBody coll (A.Only _ (A.Else _ p))
        =  do tell ["default:"]
              tell ["{"]
              coll
              call genProcess p
              tell ["}break;"]
              return True
    genCaseBody coll (A.Several _ ss)
        =  do seens <- mapM (genCaseBody coll) ss
              return $ or seens
--}}}
--{{{  while
cgenWhile :: A.Expression -> A.Process -> CGen ()
cgenWhile e p
    =  do tell ["while("]
          call genExpression e
          tell ["){"]
          call genProcess p
          tell ["}"]
--}}}
--{{{  par
-- FIXME: The ParMode is now ignored (as it is in occ21), so PRI PAR behaves
-- the same as PAR.
cgenPar :: A.ParMode -> A.Structured A.Process -> CGen ()
cgenPar pm s
    =  do bar <- csmLift $ makeNonce emptyMeta "par_barrier"
          tell ["LightProcBarrier ", bar, ";"]
          let count = countStructured s
          wss <- csmLift $ makeNonce emptyMeta "wss"
          tell ["Workspace* ",wss,"=(Workspace*)malloc(sizeof(int)*"]
          call genExpression count
          tell [");"]
          tell ["int ",wss,"_count=0;"]

          tell ["LightProcBarrierInit(wptr,&", bar, ","]
          call genExpression count
          tell [");"]

          call genStructured NotTopLevel s (startP bar wss)

          tell ["LightProcBarrierWait (wptr, &", bar, ");\n"]

          tell ["{int i;for(i=0;i<"]
          call genExpression count
          tell [";i++){TockProcFree(wptr, ", wss, "[i]);}}"]
          tell ["free(", wss, ");"]
  where
    startP :: String -> String -> Meta -> A.Process -> CGen ()
    startP bar wss _ (A.ProcCall _ n as)
        =  do (A.Proc _ _ fs _) <- specTypeOfName n
              (ws, func) <- cgenProcAlloc n fs as
              tell ["LightProcStart (wptr, &", bar, ", ", ws, ", "]
              func
              tell [");"]
              tell [wss,"[",wss,"_count++]=", ws,";"]
--}}}
--{{{  alt
cgenAlt :: Bool -> A.Structured A.Alternative -> CGen ()
cgenAlt isPri s
    =  do id <- csmLift $ makeNonce emptyMeta "alt_id"
          tell ["int ", id, " = 0;\n"]

          let isTimerAlt = containsTimers s
          tell [if isTimerAlt then "TimerAlt" else "Alt", " (wptr);\n"]
          tell ["{\n"]
          genAltEnable id s
          tell ["}\n"]

          -- Like occ21, this is always a PRI ALT, so we can use it for both.
          tell [if isTimerAlt then "TimerAltWait" else "AltWait", " (wptr);\n"]
          tell [id, " = 0;\n"]
          tell ["{\n"]
          genAltDisable id s
          tell ["}\n"]

          fired <- csmLift $ makeNonce emptyMeta "alt_fired"
          tell ["int ", fired, " = AltEnd (wptr);\n"]
          tell [id, " = 0;\n"]
          label <- csmLift $ makeNonce emptyMeta "alt_end"
          tell ["{\n"]
          genAltProcesses id fired label s
          tell ["}\n"]
          tell [label, ":\n;\n"]
  where
    containsTimers :: A.Structured A.Alternative -> Bool
    containsTimers (A.Spec _ _ s) = containsTimers s
    containsTimers (A.ProcThen _ _ s) = containsTimers s
    containsTimers (A.Only _ a)
        = case a of
            A.Alternative _ _ _ (A.InputTimerRead _ _) _ -> True
            A.Alternative _ _ _ (A.InputTimerAfter _ _) _ -> True
            _ -> False
    containsTimers (A.Several _ ss) = or $ map containsTimers ss

    genAltEnable :: String -> A.Structured A.Alternative -> CGen ()
    genAltEnable id s = call genStructured NotTopLevel s doA >> return ()
      where
        doA _ alt
            = case alt of
                A.Alternative _ e c im _ -> withIf e $ doIn c im
                A.AlternativeSkip _ e _ -> withIf e $ tell ["AltEnableSkip (wptr,", id, "++);\n"]

        doIn c im
            = do case im of
                   A.InputTimerRead _ _ -> call genMissing "timer read in ALT"
                   A.InputTimerAfter _ time ->
                     do tell ["AltEnableTimer (wptr,", id, "++,"]
                        call genExpression time
                        tell [");\n"]
                   _ ->
                     do tell ["AltEnableChannel (wptr,", id, "++,"]
                        call genVariable c A.Abbrev
                        tell [");\n"]

    genAltDisable :: String -> A.Structured A.Alternative -> CGen ()
    genAltDisable id s = call genStructured NotTopLevel s doA >> return ()
      where
        doA _ alt
            = case alt of
                A.Alternative _ e c im _ -> withIf e $ doIn c im
                A.AlternativeSkip _ e _ -> withIf e $ tell ["AltDisableSkip (wptr,", id, "++);\n"]

        doIn c im
            = do case im of
                   A.InputTimerRead _ _ -> call genMissing "timer read in ALT"
                   A.InputTimerAfter _ time ->
                     do tell ["AltDisableTimer (wptr,", id, "++, "]
                        call genExpression time
                        tell [");\n"]
                   _ ->
                     do tell ["AltDisableChannel (wptr,", id, "++, "]
                        call genVariable c A.Abbrev
                        tell [");\n"]

    genAltProcesses :: String -> String -> String -> A.Structured A.Alternative -> CGen ()
    genAltProcesses id fired label s = call genStructured NotTopLevel s doA >> return ()
      where
        doA _ alt
            = case alt of
                A.Alternative _ e c im p -> withIf e $ doIn c im p
                A.AlternativeSkip _ e p -> withIf e $ doCheck (call genProcess p)

        doIn c im p
            = do case im of
                   A.InputTimerRead _ _ -> call genMissing "timer read in ALT"
                   A.InputTimerAfter _ _ -> doCheck (call genProcess p)
                   _ -> doCheck (call genInput c im >> call genProcess p)

        doCheck body
            = do tell ["if (", id, "++ == ", fired, ") {\n"]
                 body
                 tell ["goto ", label, ";\n"]
                 tell ["}\n"]

withIf :: A.Expression -> CGen () -> CGen ()
withIf cond body
    =  do tell ["if ("]
          call genExpression cond
          tell [") {\n"]
          body
          tell ["}\n"]
--}}}
--{{{  proc call
cgenProcCall :: A.Name -> [A.Actual] -> CGen ()
cgenProcCall n as
    =  do A.Proc _ (_, rm) _ _ <- specTypeOfName n
          externalProcs <- getCompState >>* csExternals
          let ext = lookup (A.nameName n) externalProcs
          case (rm, ext) of
            -- This is rather inefficient, because if a recursive PROC is called
            -- anywhere (from other processes as well as from itself), it will
            -- be done in a PAR.
            (A.Recursive, _) ->
              let m = A.nameMeta n
              in call genPar A.PlainPar $ A.Only m $ A.ProcCall m n as
            (_, Just (ExternalOldStyle, _)) ->
                 do let (c:cs) = A.nameName n
                    tell ["{int ext_args[] = {"]
                    -- We don't use the formals in csExternals because they won't
                    -- have had array sizes added:
                    (A.Proc _ _ fs _) <- specTypeOfName n
                    call genActuals fs as
                    tell ["};"]
                    
                    case c of
                      'B' -> tell ["ExternalCallN("]
                      'C' -> tell ["BlockingCallN(wptr,"]
                      _ -> dieP (A.nameMeta n) "Unknown external PROC format"
                    tell [ [if c == '.' then '_' else c | c <- cs]
                         , ",1,ext_args);}"]
                    
            _ -> do genName n
                    tell [" (wptr", if null as then "" else ","]
                    (A.Proc _ _ fs _) <- specTypeOfName n
                    call genActuals fs as
                    tell [");\n"]
--}}}
--{{{  intrinsic procs
cgenIntrinsicProc :: Meta -> String -> [A.Actual] -> CGen ()
cgenIntrinsicProc m "ASSERT" [A.ActualExpression e] = call genAssert m e
cgenIntrinsicProc _ "RESCHEDULE" [] = call genReschedule
cgenIntrinsicProc m s as = case lookup s intrinsicProcs of
  Just amtns -> do tell ["occam_", [if c == '.' then '_' else c | c <- s], "(wptr,"]
                   when (s == "RESIZE.MOBILE.ARRAY.1D") $
                     do let mob = head as
                        A.Mobile (A.Array _ t) <- astTypeOf mob
                        call genBytesIn m t (Left False)
                        tell [","]
                   seqComma [call genActual (A.Formal am t (A.Name emptyMeta n)) a
                            | ((am, t, n), a) <- zip amtns as]
                   tell [");"]
  Nothing -> call genMissing $ "intrinsic PROC " ++ s

cgenReschedule :: CGen ()
cgenReschedule = tell ["Reschedule (wptr);"]

cgenAssert :: Meta -> A.Expression -> CGen ()
cgenAssert m e
    =  do tell ["if (!"]
          call genExpression e
          tell [") {\n"]
          call genStop m "assertion failed"
          tell ["}\n"]
--}}}
--}}}

--{{{ mobiles
cgenAllocMobile :: Meta -> A.Type -> Maybe A.Expression -> CGen()
cgenAllocMobile m (A.Mobile t@(A.Array ds innerT)) Nothing
  = do tell ["MTAllocDataArray(wptr,"]
       call genBytesIn m innerT (Left False)
       tell [",", show $ length ds]
       prefixComma $ [call genExpression e | A.Dimension e <- ds]
       tell [")"]
cgenAllocMobile m (A.Mobile t) Nothing
  = do tell ["MTAlloc(wptr,"]
       mobileElemType False t
       tell [","]
       call genBytesIn m t (Left False)
       tell [")"]
cgenAllocMobile m t@(A.Record n) Nothing
  = do isMobile <- recordAttr m t >>* A.mobileRecord
       if isMobile
         then do tell ["MTAlloc(wptr,"]
                 mobileElemType False t
                 tell [","]
                 genName n
                 tell ["_mtsize)"]
         else dieP m "Attempted to allocate a non-mobile record type"

--TODO add a pass, just for C, that pulls out the initialisation expressions for mobiles
-- into a subsequent assignment
cgenAllocMobile _ _ _ = call genMissing "Mobile allocation with initialising-expression"

-- The Bool is True if inside an array, False otherwise
mobileElemType :: Bool -> A.Type -> CGen ()
mobileElemType _ (A.Record n)
  = do tell ["(word)"]
       genName n
       tell ["_mttype"]
mobileElemType b A.Int = mobileElemType b cIntReplacement
mobileElemType b A.Bool = mobileElemType b A.Byte
-- CCSP only supports NUM with MTAlloc inside arrays:
mobileElemType True t = tell ["MT_MAKE_NUM(MT_NUM_", showOccam t,")"]
mobileElemType False t = tell ["MT_SIMPLE|MT_MAKE_TYPE(MT_DATA)"]

cgenClearMobile :: Meta -> A.Variable -> CGen ()
cgenClearMobile _ v
  = do tell ["if("]
       genVar
       tell ["!=NULL){MTRelease(wptr,(void*)"]
       genVar
       tell [");"]
       genVar
       tell ["=NULL;}"]
  where
    genVar = call genVariable v A.Original

cgenCloneMobile :: Meta -> A.Expression -> CGen ()
cgenCloneMobile _ e
  = do tell ["MTClone(wptr,(void*)"]
       call genExpression e
       tell [")"]

--}}}
