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

-- | The function dictionary and various types/helper functions for backends based around C
module GenerateCBased where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Generics

import qualified AST as A
import CompState
import Errors
import Metadata
import Pass
import qualified Properties as Prop
import TLP

cCppCommonPreReq :: [Property]
cCppCommonPreReq =
 [Prop.afterRemoved
 ,Prop.arrayLiteralsExpanded
 ,Prop.assignFlattened
 ,Prop.assignParRemoved
 ,Prop.freeNamesToArgs
 ,Prop.functionCallsRemoved
 ,Prop.functionsRemoved
 ,Prop.inputCaseRemoved
 ,Prop.mainTagged
 ,Prop.nestedPulled
 ,Prop.outExpressionRemoved
 ,Prop.parsWrapped
 ,Prop.parUsageChecked
 ,Prop.subscriptsPulledUp
 ,Prop.typesResolvedInAST
 ,Prop.typesResolvedInState
 ]


--{{{  monad definition
type CGen' = WriterT [String] PassM
type CGen = ReaderT GenOps CGen'

instance Die CGen where
  dieReport = throwError
  
instance CSMR m => CSMR (ReaderT GenOps m) where
  getCompState = lift getCompState
--}}}

-- | A function that applies a subscript to a variable.
type SubscripterFunction = A.Variable -> A.Variable

--{{{  generator ops
-- | Operations for turning various things into C.
-- These are in a structure so that we can reuse operations in other
-- backends without breaking the mutual recursion.
data GenOps = GenOps {
    -- | Declares the C array of sizes for an occam array.
    declareArraySizes :: A.Type -> A.Name -> CGen (),
    -- | Generates code when a variable goes out of scope (e.g. deallocating memory).
    declareFree :: Meta -> A.Type -> A.Variable -> Maybe (CGen ()),
    -- | Generates code when a variable comes into scope (e.g. allocating memory, initialising variables).
    declareInit :: Meta -> A.Type -> A.Variable -> Maybe A.Expression -> Maybe (CGen ()),
    -- | Generates an individual parameter to a function\/proc.
    genActual :: A.Actual -> CGen (),
    -- | Generates the list of actual parameters to a function\/proc.
    genActuals :: [A.Actual] -> CGen (),
    genAllocMobile :: Meta -> A.Type -> Maybe A.Expression -> CGen(),
    genAlt :: Bool -> A.Structured A.Alternative -> CGen (),
    -- | Generates the given array element expressions as a flattened (one-dimensional) list of literals
    genArrayLiteralElems :: [A.ArrayElem] -> CGen (),
    -- | Declares a constant array for the sizes (dimensions) of a C array.
    genArraySize :: Bool -> CGen () -> A.Name -> CGen (),
    -- | Writes out the dimensions of an array, that can be used to initialise the sizes of an array.  Fails if there is an 'A.UnknownDimension' present.
    genArraySizesLiteral :: A.Name -> A.Type -> CGen (),
    -- | Writes out the actual data storage array name.
    genArrayStoreName :: A.Name -> CGen(),
    -- | Generates an array subscript for the given variable (with error checking if the Bool is True), using the given expression list as subscripts
    genArraySubscript :: Bool -> A.Variable -> [A.Expression] -> CGen (),
    genAssert :: Meta -> A.Expression -> CGen (),
    -- | Generates an assignment statement with a single destination and single source.
    genAssign :: Meta -> [A.Variable] -> A.ExpressionList -> CGen (),
    -- | Generates the number of bytes in a fixed size type, fails if a free dimension is present and is not allowed.
    -- The Either parameter is either an array variable (to use the _sizes array of) or a boolean specifying
    -- wheter or not one free dimension is allowed (True <=> allowed).
    genBytesIn :: Meta -> A.Type -> Either Bool A.Variable -> CGen (),
    -- | Generates a case statement over the given expression with the structured as the body.
    genCase :: Meta -> A.Expression -> A.Structured A.Option -> CGen (),
    genCheckedConversion :: Meta -> A.Type -> A.Type -> CGen () -> CGen (),
    genClearMobile :: Meta -> A.Variable -> CGen (),
    genConversion :: Meta -> A.ConversionMode -> A.Type -> A.Expression -> CGen (),
    genConversionSymbol :: A.Type -> A.Type -> A.ConversionMode -> CGen (),
    genDecl :: A.AbbrevMode -> A.Type -> A.Name -> CGen (),
    genDeclType :: A.AbbrevMode -> A.Type -> CGen (),
    -- | Generates a declaration of a variable of the specified type and name.  
    -- The Bool indicates whether the declaration is inside a record (True) or not (False).
    genDeclaration :: A.Type -> A.Name -> Bool -> CGen (),
    genDirectedVariable :: CGen () -> A.Direction -> CGen (),
    genDyadic :: Meta -> A.DyadicOp -> A.Expression -> A.Expression -> CGen (),
    genExpression :: A.Expression -> CGen (),
    genFlatArraySize :: [A.Dimension] -> CGen (),
    genFormal :: A.Formal -> CGen (),
    genFormals :: [A.Formal] -> CGen (),
    genForwardDeclaration :: A.Specification -> CGen(),
    genFuncDyadic :: Meta -> String -> A.Expression -> A.Expression -> CGen (),
    genFuncMonadic :: Meta -> String -> A.Expression -> CGen (),
    -- | Gets the current time into the given variable
    genGetTime :: Meta -> A.Variable -> CGen (),
    -- | Generates an IF statement (which can have replicators, specifications and such things inside it).
    genIf :: Meta -> A.Structured A.Choice -> CGen (),
    genInput :: A.Variable -> A.InputMode -> CGen (),
    genInputItem :: A.Variable -> A.InputItem -> CGen (),
    genIntrinsicFunction :: Meta -> String -> [A.Expression] -> CGen (),
    genIntrinsicProc :: Meta -> String -> [A.Actual] -> CGen (),
    genLiteral :: A.LiteralRepr -> A.Type -> CGen (),
    genLiteralRepr :: A.LiteralRepr -> A.Type -> CGen (),
    genMissing :: String -> CGen (),
    genMissingC :: CGen String -> CGen (),
    genMonadic :: Meta -> A.MonadicOp -> A.Expression -> CGen (),
    -- | Generates an output statement.
    genOutput :: A.Variable -> [A.OutputItem] -> CGen (),
    -- | Generates an output statement for a tagged protocol.
    genOutputCase :: A.Variable -> A.Name -> [A.OutputItem] -> CGen (),
    -- | Generates an output for an individual item.
    genOutputItem :: A.Variable -> A.OutputItem -> CGen (),
    -- | Generates a loop that maps over every element in a (potentially multi-dimensional) array
    genOverArray :: Meta -> A.Variable -> (SubscripterFunction -> Maybe (CGen ())) -> CGen (),
    genPar :: A.ParMode -> A.Structured A.Process -> CGen (),
    genProcCall :: A.Name -> [A.Actual] -> CGen (),
    genProcess :: A.Process -> CGen (),
    genRecordTypeSpec :: A.Name -> Bool -> [(A.Name, A.Type)] -> CGen (),
    -- | Generates a replicator loop, given the replicator and body
    genReplicator :: A.Replicator -> CGen () -> CGen (),
    -- | Generates the three bits of a for loop (e.g. "int i=0;i<10;i++" for the given replicator
    genReplicatorLoop :: A.Replicator -> CGen (),
    genRetypeSizes :: Meta -> A.Type -> A.Name -> A.Type -> A.Variable -> CGen (),
    genSeq :: A.Structured A.Process -> CGen (),
    genSimpleDyadic :: String -> A.Expression -> A.Expression -> CGen (),
    genSimpleMonadic :: String -> A.Expression -> CGen (),
    genSizeSuffix :: String -> CGen (),
    genSlice :: A.Variable -> A.Expression -> A.Expression -> [A.Dimension] -> (CGen (), A.Name -> CGen ()),
    genSpec :: A.Specification -> CGen () -> CGen (),
    genSpecMode :: A.SpecMode -> CGen (),
    -- | Generates a STOP process that uses the given Meta tag and message as its printed message.
    genStop :: Meta -> String -> CGen (),
    genStructured :: forall a. Data a => A.Structured a -> (Meta -> a -> CGen ()) -> CGen (),
    genTLPChannel :: TLPChannel -> CGen (),
    genTimerRead :: A.Variable -> A.Variable -> CGen (),
    genTimerWait :: A.Expression -> CGen (),
    genTopLevel :: A.AST -> CGen (),
    -- | Generates the type as it might be used in a cast expression
    genType :: A.Type -> CGen (),
    genTypeSymbol :: String -> A.Type -> CGen (),
    genUnfoldedExpression :: A.Expression -> CGen (),
    genUnfoldedVariable :: Meta -> A.Variable -> CGen (),
    -- | Generates a variable, with indexing checks if needed
    genVariable :: A.Variable -> CGen (),
    genVariableAM :: A.Variable -> A.AbbrevMode -> CGen (),
    -- | Generates a variable, with no indexing checks anywhere
    genVariableUnchecked :: A.Variable -> CGen (),
    -- | Performs a wait for\/until (depending on the 'A.WaitMode') a specified time
    genWait :: A.WaitMode -> A.Expression -> CGen (),
    -- | Generates a while loop with the given condition and body.
    genWhile :: A.Expression -> A.Process -> CGen (),
    getScalarType :: A.Type -> Maybe String,
    introduceSpec :: A.Specification -> CGen (),
    removeSpec :: A.Specification -> CGen ()
  }

-- | Call an operation in GenOps.
class CGenCall a where
  call :: (GenOps -> a) -> a

instance CGenCall (a -> CGen z) where
--  call :: (a -> CGen b) -> a -> CGen b
  call f x0 = do ops <- ask
                 f ops x0

instance CGenCall (a -> b -> CGen z) where
  call f x0 x1
    = do ops <- ask
         f ops x0 x1

instance CGenCall (a -> b -> c -> CGen z) where
  call f x0 x1 x2
    = do ops <- ask
         f ops x0 x1 x2

instance CGenCall (a -> b -> c -> d -> CGen z) where
  call f x0 x1 x2 x3
    = do ops <- ask
         f ops x0 x1 x2 x3

instance CGenCall (a -> b -> c -> d -> e -> CGen z) where
  call f x0 x1 x2 x3 x4
    = do ops <- ask
         f ops x0 x1 x2 x3 x4

-- A bit of a mind-boggler, but this is essentially for genSlice
instance CGenCall (a -> b -> c -> d -> (CGen x, y -> CGen z)) where
  call f x0 x1 x2 x3
    = (do ops <- ask
          fst $ f ops x0 x1 x2 x3
      ,\y -> do ops <- ask
                (snd $ f ops x0 x1 x2 x3) y
      )

fget :: (GenOps -> a) -> CGen a
fget = asks

