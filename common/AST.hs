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

-- | Data types for occam abstract syntax.
-- This is intended to be imported qualified as A.
module AST where

{-! global : Haskell2Xml !-}

import Data.Generics

import Metadata

-- | The general type of a name.
-- This is used by the parser to indicate what sort of name it's expecting in a
-- particular context; in later passes you can look at how the name is actually
-- defined, which is more useful.
data NameType =
  ChannelName | DataTypeName | FunctionName | FieldName | PortName
  | ProcName | ProtocolName | RecordName | TagName | TimerName | VariableName
  deriving (Show, Eq, Typeable, Data)

-- | An identifier defined in the source code.
-- This can be any of the 'NameType' types.
data Name = Name {
    -- | Metadata.
    nameMeta :: Meta,
    -- | The general type of the name.
    nameType :: NameType,
    -- | The internal version of the name.
    -- This isn't necessary the same as it appeared in the source code; if
    -- you're displaying it to the user in an error message, you should
    -- probably look up the original name in the corresponding 'NameDef'.
    nameName :: String
  }
  deriving (Typeable, Data)

instance Show Name where
  show n = show $ nameName n

instance Eq Name where
  (==) a b = nameName a == nameName b

instance Ord Name where
  compare a b = compare (nameName a) (nameName b)

-- | The definition of a name.
data NameDef = NameDef {
    -- | Metadata.
    ndMeta :: Meta,
    -- | The internal version of the name.
    ndName :: String,
    -- | The name as it appeared in the source code.
    -- This can be used for error reporting.
    ndOrigName :: String,
    -- | The general type of the name.
    ndNameType :: NameType,
    -- | The specification type of the name's definition (see 'SpecType').
    ndType :: SpecType,
    -- | The abbreviation mode of the name's definition (see 'AbbrevMode').
    ndAbbrevMode :: AbbrevMode,
    -- | The placement mode of the name's definition (see 'Placement').
    ndPlacement :: Placement
  }
  deriving (Show, Eq, Typeable, Data)

-- | The direction of a channel.
data Direction =
  DirInput         -- ^ The input end.
  | DirOutput      -- ^ The output end.
  | DirUnknown     -- ^ Either direction; either this is a whole channel,
                   -- or its direction is to be figured out later.
  deriving (Show, Eq, Typeable, Data)

-- | Attributes of the type of a channel.
data ChanAttributes = ChanAttributes {
    caWritingShared :: Bool,
    caReadingShared :: Bool
  }
  deriving (Show, Eq, Typeable, Data)

-- | A data or protocol type.
-- The two concepts aren't unified in occam, but they are here, because it
-- makes sense to be able to ask what type a particular name is defined to
-- have.
data Type =
  Bool                                      -- ^ Boolean
  | Byte                                    -- ^ 8-bit unsigned integer
  | UInt16                                  -- ^ 16-bit unsigned integer
  | UInt32                                  -- ^ 32-bit unsigned integer
  | UInt64                                  -- ^ 64-bit unsigned integer
  | Int                                     -- ^ Most efficient signed integer
  | Int8                                    -- ^ 8-bit signed integer
  | Int16                                   -- ^ 16-bit signed integer
  | Int32                                   -- ^ 32-bit signed integer
  | Int64                                   -- ^ 64-bit signed integer
  | Real32                                  -- ^ IEEE single-length float
  | Real64                                  -- ^ IEEE double-length float
  -- | An array.
  -- For N-dimensional arrays, the [Dimension] list will be of length N.
  | Array [Dimension] Type
  -- | A user-defined data type.
  | UserDataType Name
  -- | A record type.
  | Record Name
  -- | A user-defined protocol.
  | UserProtocol Name
  -- | A channel of the specified type.
  | Chan Direction ChanAttributes Type
  -- | A counted input or output.
  | Counted Type Type
  | Any
  | Timer
  | Time
  | Port Type
  | Mobile Type
  deriving (Show, Eq, Typeable, Data)

-- | An array dimension.
-- Depending on the context, an array type may have empty dimensions, which is
-- why this isn't just an Int.
data Dimension =
  Dimension Int
  | UnknownDimension
  deriving (Show, Eq, Typeable, Data)

-- | How a variable is placed in memory.
-- Placement is used in occam to map preexisting memory and IO space to
-- variables.
data Placement =
  -- | No placement -- allocate the variable as usual.
  -- Traditional occam compilers will allocate the variable either in the
  -- workspace or in vectorspace as appropriate.
  Unplaced
  -- | Allocate in the workspace (i.e. on the stack).
  | PlaceInWorkspace
  -- | Allocate in vectorspace (i.e. on the heap).
  | PlaceInVecspace
  -- | Use an existing address.
  | PlaceAt Expression
  deriving (Show, Eq, Typeable, Data)

-- | Data type conversion modes.
-- Which of these are legal depends on the type; in general you only use modes
-- other than 'DefaultConversion' when going to or from floating-point types.
data ConversionMode =
  DefaultConversion
  | Round
  | Trunc
  deriving (Show, Eq, Typeable, Data)

-- | A subscript that can be applied to a variable or an expression.
data Subscript =
  -- | Select a single element of an array.
  Subscript Meta Expression
  -- | Select a named field of a record type.
  | SubscriptField Meta Name
  -- | Select a slice of an array.
  -- The first 'Expression' is the @FROM@; the initial value to begin at,
  -- inclusive.
  -- The second 'Expression' is the @FOR@; the count of items to include in the
  -- slice.
  | SubscriptFromFor Meta Expression Expression
  -- | Like 'SubscriptFromFor', but without a @FOR@; it goes to the end of the
  -- array.
  | SubscriptFrom Meta Expression
  -- | Like 'SubscriptFromFor', but without a @FROM@; it starts from the
  -- beginning of the array.
  | SubscriptFor Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | The representation of a literal.
data LiteralRepr =
  RealLiteral Meta String
  | IntLiteral Meta String
  | HexLiteral Meta String
  | ByteLiteral Meta String
  | ArrayLiteral Meta [ArrayElem]
  | RecordLiteral Meta [Expression]
  deriving (Show, Eq, Typeable, Data)

-- | An item inside an array literal -- which might be an expression, or might
-- be a nested array. (occam multidimensional arrays are not arrays of arrays,
-- which is why we can't just use nested Literals.)
data ArrayElem =
  ArrayElemArray [ArrayElem]
  | ArrayElemExpr Expression
  deriving (Show, Eq, Typeable, Data)

-- | A variable.
data Variable =
  -- | A plain variable (e.g. @c@).
  Variable Meta Name
  -- | A subscripted variable (e.g. @c[0]@ or @person[name]@).
  | SubscriptedVariable Meta Subscript Variable
  -- | A channel-end variable (e.g. @c?@)
  | DirectedVariable Meta Direction Variable
  -- | A dereferenced mobile variable (e.g. using MOBILE INT as INT)
  | DerefVariable Meta Variable
  deriving (Show, Eq, Typeable, Data)

-- | An array constructor expression.
data ArrayConstr =
  -- | A simple integer range, beginning at the first value (inclusive) and ending at the second value (inclusive), with stepping 1.
  -- If the first value is bigger than the second, the effective value is an empty array.
  -- This will be transformed by an early pass into the second form (RepConstr).
  RangeConstr Meta Expression Expression
  -- | A more general and powerful array constructor as used in occam-pi.
  -- The first item is the replicator, the second is the expression
  | RepConstr Meta Replicator Expression
  deriving (Show, Eq, Typeable, Data)


-- | An expression.
data Expression =
  -- | A monadic (unary) operator.
  Monadic Meta MonadicOp Expression
  -- | A dyadic (binary) operator.
  | Dyadic Meta DyadicOp Expression Expression
  -- | The most positive value of a given type.
  | MostPos Meta Type
  -- | The most negative value of a given type.
  | MostNeg Meta Type
  -- | The size of the outermost dimension of an array type (see 'SizeExpr').
  | SizeType Meta Type
  -- | The size of the outermost dimension of an array expression.
  -- Given @[8][4]INT a:@, @SIZE a@ is 8 and @SIZE a[0]@ is 4.
  | SizeExpr Meta Expression
  -- | The size of the outermost dimension of an array variable (see 'SizeExpr').
  | SizeVariable Meta Variable
  | Conversion Meta ConversionMode Type Expression
  | ExprVariable Meta Variable
  | Literal Meta Type LiteralRepr
  | True Meta
  | False Meta
  | FunctionCall Meta Name [Expression]
  | IntrinsicFunctionCall Meta String [Expression]
  | SubscriptedExpr Meta Subscript Expression
  | BytesInExpr Meta Expression
  | BytesInType Meta Type
  | OffsetOf Meta Type Name
  | ExprConstr Meta ArrayConstr
  deriving (Show, Eq, Typeable, Data)

-- | A list of expressions.
data ExpressionList =
  -- | A list of expressions resulting from a function call.
  FunctionCallList Meta Name [Expression]
  -- | A list of expressions resulting from, well, a list of expressions.
  | ExpressionList Meta [Expression]
  deriving (Show, Eq, Typeable, Data)

-- | A monadic (unary) operator.
-- Nothing to do with Haskell monads.
data MonadicOp =
  MonadicSubtr
  | MonadicMinus
  | MonadicBitNot
  | MonadicNot
  deriving (Show, Eq, Typeable, Data)

-- | A dyadic (binary) operator.
data DyadicOp =
  Add | Subtr | Mul | Div | Rem
  | Plus | Minus | Times
  | BitAnd | BitOr | BitXor
  | LeftShift | RightShift
  | And | Or
  | Eq | NotEq | Less | More | LessEq | MoreEq
  | After
  deriving (Show, Eq, Typeable, Data)

-- | An item in an input.
data InputItem =
  -- | A counted input.
  -- The count is read into the first variable, and the array items into the second.
  InCounted Meta Variable Variable
  -- | A simple input into a single variable.
  | InVariable Meta Variable
  deriving (Show, Eq, Typeable, Data)

-- | An item in an output -- the counterpart of 'InputItem'.
data OutputItem =
  -- | A counted output.
  -- The count is the first expression; the array items are the second.
  OutCounted Meta Expression Expression
  -- | A simple output from an expression.
  | OutExpression Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | A replicator.
data Replicator = 
  -- | Count up in 1s from a start value.
  -- The 'Name' names the replicator index, the first expression is the base
  -- and the second expression is the count.
  For Meta Name Expression Expression
  -- | Iterate over a list.
  -- The 'Name' names the loop variable and the expression is the list to
  -- iterate over.
  | ForEach Meta Name Expression
  deriving (Show, Eq, Typeable, Data)

-- | A choice in an @IF@ process.
data Choice = Choice Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

-- | A mode of waiting -- either for a specified duration, or until a specified time.
data WaitMode =
  WaitFor
  | WaitUntil
  deriving (Show, Eq, Typeable, Data)

-- | A guard in an @ALT@.
data Alternative =
  -- | A plain guard.
  -- The channel or timer is the 'Variable', and the destination (or @AFTER@
  -- clause) is inside the 'InputMode'. The process is the body of the guard.
  Alternative Meta Variable InputMode Process
  -- | A conditional guard.
  -- The 'Expression' is the pre-condition, everything else is as 'Alternative'
  -- above.
  | AlternativeCond Meta Expression Variable InputMode Process
  -- | A @SKIP@ guard (one that is always ready).
  -- The 'Expression' is the pre-condition.
  | AlternativeSkip Meta Expression Process
  -- | A @wait for@\/@until@ guard.
  | AlternativeWait Meta WaitMode Expression Process
  deriving (Show, Eq, Typeable, Data)

-- | An option in a @CASE@ process.
data Option =
  -- | A regular option.
  -- These can match multiple values.
  Option Meta [Expression] Process
  -- | A default option, used if nothing else matches.
  -- It does not have to be the last option.
  | Else Meta Process
  deriving (Show, Eq, Typeable, Data)

-- | An option in a @? CASE@ process.
-- The name is the protocol tag, followed by zero or more input items, followed
-- by the process to be executed if that option is matched.
data Variant = Variant Meta Name [InputItem] Process
  deriving (Show, Eq, Typeable, Data)

-- | This represents something that can contain local replicators and specifications.
-- (This ought to be a parametric type, @Structured Variant@ etc., but doing so
-- makes using generic functions across it hard.)
data Structured =
  Rep Meta Replicator Structured
  | Spec Meta Specification Structured
  | ProcThen Meta Process Structured
  | OnlyV Meta Variant                  -- ^ Variant (@CASE@) input process
  | OnlyC Meta Choice                   -- ^ @IF@ process
  | OnlyO Meta Option                   -- ^ @CASE@ process
  | OnlyA Meta Alternative              -- ^ @ALT@ process
  | OnlyP Meta Process                  -- ^ @SEQ@, @PAR@
  | OnlyEL Meta ExpressionList          -- ^ @VALOF@
  | Several Meta [Structured]
  deriving (Show, Eq, Typeable, Data)

-- | The mode in which an input operates.
data InputMode =
  -- | A plain input from a channel.
  InputSimple Meta [InputItem]
  -- | A variant input from a channel.
  | InputCase Meta Structured
  -- | Read the value of a timer.
  | InputTimerRead Meta InputItem
  -- | Wait for a particular time to go past on a timer.
  | InputTimerAfter Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | Abbreviation mode.
-- This describes how a name is being accessed.
-- In the future this will have additional modes for @RESULT@, @INITIAL@, etc.
data AbbrevMode =
  -- | The original declaration of a name.
  Original
  -- | An abbreviation by reference.
  | Abbrev
  -- | An abbreviation by value.
  | ValAbbrev
  deriving (Show, Eq, Typeable, Data)

-- | Anything that introduces a new name.
data Specification =
  Specification Meta Name SpecType
  deriving (Show, Eq, Typeable, Data)

-- | The type of a 'Specification'.
data SpecType =
  -- | Set placement for an existing variable.
  Place Meta Expression
  -- | Declare a variable.
  | Declaration Meta Type
  -- | Declare an abbreviation of a variable.
  | Is Meta AbbrevMode Type Variable
  -- | Declare an abbreviation of an expression.
  | IsExpr Meta AbbrevMode Type Expression
  -- | Declare an abbreviation of an array of channels.
  | IsChannelArray Meta Type [Variable]
  -- | Declare a user data type.
  | DataType Meta Type
  -- | Declare a new record type.
  -- The 'Bool' indicates whether the record is @PACKED@.
  -- The list is the fields of the record.
  | RecordType Meta Bool [(Name, Type)]
  -- | Declare a simple protocol.
  -- The list contains the types of the items.
  | Protocol Meta [Type]
  -- | Declare a variant protocol.
  -- The list pairs tag names with item types.
  | ProtocolCase Meta [(Name, [Type])]
  -- | Declare a @PROC@.
  | Proc Meta SpecMode [Formal] Process
  -- | Declare a @FUNCTION@.
  | Function Meta SpecMode [Type] [Formal] Structured
  -- | Declare a retyping abbreviation of a variable.
  | Retypes Meta AbbrevMode Type Variable
  -- | Declare a retyping abbreviation of an expression.
  | RetypesExpr Meta AbbrevMode Type Expression
  deriving (Show, Eq, Typeable, Data)

-- | Specification mode for @PROC@s and @FUNCTION@s.
-- This indicates whether a function is inlined by the compiler.
data SpecMode =
  PlainSpec | InlineSpec
  deriving (Show, Eq, Typeable, Data)

-- | Formal parameters for @PROC@s and @FUNCTION@s.
data Formal =
  Formal AbbrevMode Type Name
  deriving (Show, Eq, Typeable, Data)

-- | Actual parameters for @PROC@s and @FUNCTION@s.
data Actual =
  -- | A variable used as a parameter.
  -- 'AbbrevMode' and 'Type' are here for parity with 'Formal'; they can be
  -- figured out from the variable.
  ActualVariable AbbrevMode Type Variable
  -- | An expression used as a parameter.
  | ActualExpression Type Expression
  deriving (Show, Eq, Typeable, Data)

-- | The mode in which a @PAR@ operates.
data ParMode =
  -- | Regular @PAR@.
  PlainPar
  -- | Prioritised @PAR@.
  -- Earlier processes run at higher priority.
  | PriPar
  -- | Placed @PAR@.
  -- 'Processor' instances inside this indicate which processor each parallel
  -- process runs on.
  | PlacedPar
  deriving (Show, Eq, Typeable, Data)

-- | A process.
data Process =
  Assign Meta [Variable] ExpressionList
  | Input Meta Variable InputMode
  | Output Meta Variable [OutputItem]
  | OutputCase Meta Variable Name [OutputItem]
  | GetTime Meta Variable
  | Wait Meta WaitMode Expression
  | Skip Meta
  | Stop Meta
  | Seq Meta Structured
  | If Meta Structured
  | Case Meta Expression Structured
  | While Meta Expression Process
  | Par Meta ParMode Structured
  -- | A @PROCESSOR@ process.
  -- The occam2.1 syntax says this is just a process, although it shouldn't be
  -- legal outside a @PLACED PAR@.
  | Processor Meta Expression Process
  | Alt Meta Bool Structured
  | ProcCall Meta Name [Actual]
  -- | A call of a built-in @PROC@.
  -- This may go away in the future, since which @PROC@s are intrinsics depends
  -- on the backend.
  | IntrinsicProcCall Meta String [Actual]
  deriving (Show, Eq, Typeable, Data)

