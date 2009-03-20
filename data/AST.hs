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

-- | Data types for occam abstract syntax.
-- This is intended to be imported qualified as A.
--
-- All types with only no-argument constructors may (and should) derive Ord
-- automatically, but for all other types the Ord instance is in the OrdAST
-- module.
module AST where

{-! global : Haskell2Xml !-}

import Data.Generics

import Metadata

-- | An identifier defined in the source code.
data Name = Name {
    -- | Metadata.
    nameMeta :: Meta,
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
  (==) a b = (nameName a) == (nameName b)

-- | The definition of a name.
data NameDef = NameDef {
    -- | Metadata for where the name was originally defined.
    ndMeta :: Meta,
    -- | The internal version of the name.
    ndName :: String,
    -- | The name as it appeared in the source code.
    -- This can be used for error reporting.
    ndOrigName :: String,
    -- | The specification type of the name's definition (see 'SpecType').
    ndSpecType :: SpecType,
    -- | The abbreviation mode of the name's definition (see 'AbbrevMode').
    ndAbbrevMode :: AbbrevMode,
    -- | The source of the name (see 'NameSource').
    ndNameSource :: NameSource,
    -- | The placement mode of the name's definition (see 'Placement').
    ndPlacement :: Placement
  }
  deriving (Show, Eq, Typeable, Data)

data NameSource
  = NameUser       -- ^ A name from the source program
  | NameNonce      -- ^ A name the compiler generated
  | NamePredefined -- ^ A magic name without definition (e.g. the Rain timer)
  deriving (Show, Eq, Typeable, Data)

-- | The direction of a channel.
data Direction =
  DirInput         -- ^ The input end.
  | DirOutput      -- ^ The output end.
  deriving (Show, Eq, Typeable, Data)

-- | Attributes of the type of a channel.
data ChanAttributes = ChanAttributes {
    caWritingShared :: Bool,
    caReadingShared :: Bool
  }
  deriving (Show, Eq, Typeable, Data)

-- | In future we will probably add more timers to this list, especially for
-- occam.  But for now we just differentiate between an occam timer (which
-- reads into something of type Int), and a Rain timer (which reads into something
-- of type Time).
data TimerType = OccamTimer | RainTimer
  deriving (Eq, Show, Typeable, Data)

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
  -- | A (linked) list that allows element-wise removal, and easy
  -- concatentation.  Has dynamic size.
  | List Type
  -- | A user-defined data type.
  | UserDataType Name
  -- | A record type.
  | Record Name
  -- | A user-defined protocol.
  | UserProtocol Name
  -- | A channel of the specified type.
  | Chan ChanAttributes Type
  -- | A channel end of the specified type.
  | ChanEnd Direction ChanAttributes Type
  -- | A counted input or output.
  -- The first type is that of the count; the second is that of the array.
  -- (For example, @INT::[]BYTE@ would be @A.Counted A.Int (A.Array ...)@).
  | Counted Type Type
  | Any
  | Timer TimerType
  | Time
  | Port Type
  | Mobile Type
  -- | A type that will be inferred automatically by a pass.
  | Infer
  -- | A type that will be inferred by type unification.  Either for a named
  -- variable, or for an anonymous, uniquely identified, expression
  | UnknownVarType TypeRequirements (Either Name (Meta, Int))
  -- | A numeric type to be inferred later, that must be able to hold the given
  -- value.  The Int is a unique identifier, the Integer is the number to hold
  | UnknownNumLitType Meta Int Integer
  deriving (Show, Eq, Typeable, Data)

data TypeRequirements = TypeRequirements
  { mustBePoisonable :: Bool }
  deriving (Show, Eq, Typeable, Data)

-- | An array dimension.
-- Depending on the context, an array type may have empty dimensions, which is
-- why this isn't just an Expression.
data Dimension =
  Dimension Expression
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

-- | Which ends (or both) of an array dimension to check the subscript against.
-- By default, all subscripts in occam have the CheckBoth mode, but
-- control-flow analysis may reduce the checking.  Also, the user will have the
-- ability to turn off checks.  Finally, checks introduced by passes may well
-- use NoCheck if the array index is known to be within bounds.
data SubscriptCheck =
  NoCheck
  | CheckLower
  | CheckUpper
  | CheckBoth
  deriving (Show, Eq, Typeable, Data)

-- | A subscript that can be applied to a variable or an expression.
data Subscript =
  -- | Select a single element of an array.
  Subscript Meta SubscriptCheck Expression
  -- | Select a named field of a record type.
  | SubscriptField Meta Name
  -- | Select a slice of an array.
  -- The first 'Expression' is the @FROM@; the initial value to begin at,
  -- inclusive.
  -- The second 'Expression' is the @FOR@; the count of items to include in the
  -- slice.
  | SubscriptFromFor Meta SubscriptCheck Expression Expression
  -- | Like 'SubscriptFromFor', but without a @FOR@; it goes to the end of the
  -- array.
  | SubscriptFrom Meta SubscriptCheck Expression
  -- | Like 'SubscriptFromFor', but without a @FROM@; it starts from the
  -- beginning of the array.
  | SubscriptFor Meta SubscriptCheck Expression
  deriving (Show, Eq, Typeable, Data)

-- | The representation of a literal.
--
-- Note that ListLiteral is distinct from ArrayLiteral.  Array literals can
-- be multi-dimensional whereas list literals are always single-dimension (lists
-- of lists are valid)
data LiteralRepr =
  RealLiteral Meta String
  | IntLiteral Meta String
  | HexLiteral Meta String
  | ByteLiteral Meta String
  -- | This can be for arrays and for lists
  | ArrayListLiteral Meta (Structured Expression)
  -- | This is transformed out very early on.  The first item is the start of the
  -- range, the second is the end of the range (both inclusive)
  | RangeLiteral Meta Expression Expression
  | RecordLiteral Meta [Expression]
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
  -- | The size of the outermost dimension of an array variable (see
  -- 'SizeExpr').
  | SizeVariable Meta Variable
  -- | An array that contains all the dimensions of an array.  Hence this is different
  -- from SizeVariable which is only the outermost dimension.
  | AllSizesVariable Meta Variable
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
  -- | A mobile allocation. The type should always be Mobile t, and the
  -- Expression should be of type t.
  | AllocMobile Meta Type (Maybe Expression)
  -- | A CLONE operation.  The inner expression should have a Mobile type, and
  -- this will have the same type as the inner component:
  | CloneMobile Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | A list of expressions.
data ExpressionList =
  -- | A list of expressions resulting from a function call.
  FunctionCallList Meta Name [Expression]
  -- | A list of expressions resulting from an intrinsic function call.
  | IntrinsicFunctionCallList Meta String [Expression]
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
  | Concat
  deriving (Show, Eq, Typeable, Data)

-- | An item in an input.
data InputItem =
  -- | A counted input.
  -- The count is read into the first variable, and the array items into the
  -- second.
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
  -- | Count in steps from a start value.
  -- The first expression is the base, the second expression is the count,
  -- and the third is the step
  For Meta Expression Expression Expression
  -- | Iterate over a list.
  -- The expression is the list to iterate over.
  | ForEach Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | A choice in an @IF@ process.
data Choice = Choice Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

-- | A guard in an @ALT@.
data Alternative =
  -- | A plain or conditional guard.
  -- The channel or timer is the 'Variable', and the destination (or @AFTER@
  -- clause) is inside the 'InputMode'. The process is the body of the guard.
  -- The 'Expression' is the pre-condition.
  Alternative Meta Expression Variable InputMode Process
  -- | A @SKIP@ guard (one that is always ready).
  -- The 'Expression' is the pre-condition.
  | AlternativeSkip Meta Expression Process
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

-- | This represents something that can contain local replicators and
-- specifications.
data Data a => Structured a =
  Spec Meta Specification (Structured a)
  | ProcThen Meta Process (Structured a)
  | Only Meta a
  | Several Meta [Structured a]
  deriving (Show, Eq, Typeable)

-- The Data instance for Structured is tricky.  Because it is a parameterised
-- class we need to change the dataCast1 function from the default declaration;
-- something that leaving GHC to handle deriving (Data) will not achieve.
-- Therefore we have no choice but to provide our own instance long-hand here.

_struct_SpecConstr, _struct_ProcThenConstr,
  _struct_OnlyConstr, _struct_SeveralConstr :: Constr
_struct_DataType :: DataType

_struct_SpecConstr     = mkConstr _struct_DataType "Spec" [] Prefix
_struct_ProcThenConstr = mkConstr _struct_DataType "ProcThen" [] Prefix
_struct_OnlyConstr     = mkConstr _struct_DataType "Only" [] Prefix
_struct_SeveralConstr  = mkConstr _struct_DataType "Several" [] Prefix
_struct_DataType = mkDataType "AST.Structured"
  [ _struct_SpecConstr
  , _struct_ProcThenConstr
  , _struct_OnlyConstr
  , _struct_SeveralConstr
  ]

instance Data a => Data (Structured a) where
  gfoldl f z (Spec m sp str)  = z Spec `f` m `f` sp `f` str
  gfoldl f z (ProcThen m p s) = z ProcThen `f` m `f` p `f` s
  gfoldl f z (Only m x)       = z Only `f` m `f` x
  gfoldl f z (Several m ss)   = z Several `f` m `f` ss
  toConstr (Spec {})     = _struct_SpecConstr
  toConstr (ProcThen {}) = _struct_ProcThenConstr
  toConstr (Only {})     = _struct_OnlyConstr
  toConstr (Several {})  = _struct_SeveralConstr
  gunfold k z c = case constrIndex c of
                    1 -> (k . k . k) (z Spec)
                    2 -> (k . k . k) (z ProcThen)
                    3 -> (k . k) (z Only)
                    4 -> (k . k) (z Several)
                    _ -> error "gunfold"
  dataTypeOf _ = _struct_DataType
  dataCast1 f  = gcast1 f

-- | The mode in which an input operates.
data InputMode =
  -- | A plain input from a channel.
  InputSimple Meta [InputItem]
  -- | A variant input from a channel.
  | InputCase Meta (Structured Variant)
  -- | Read the value of a timer.
  | InputTimerRead Meta InputItem
  -- | Wait for a particular time to go past on a timer.
  | InputTimerAfter Meta Expression
  -- | Wait for a specified amount of time on a timer.
  -- Equivalent to a timer-read followed by a timer-after
  | InputTimerFor Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | Abbreviation mode.
-- This describes how a name is being accessed.
data AbbrevMode =
  -- | The original declaration of a name.
  Original
  -- | An abbreviation by reference.
  | Abbrev
  -- | An abbreviation by value.
  | ValAbbrev
  -- | An abbreviation by value that can be modified.
  | InitialAbbrev
  -- | An abbreviation by reference that is initially undefined.
  | ResultAbbrev
  deriving (Show, Eq, Typeable, Data)

-- | Anything that introduces a new name.
data Specification =
  Specification Meta Name SpecType
  deriving (Show, Eq, Typeable, Data)

-- | The type of a 'Specification'.
data SpecType =
  -- | Set placement for an existing variable.
  Place Meta Expression
  -- | Declare a variable
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
  | Proc Meta (SpecMode, RecMode) [Formal] Process
  -- | Declare a @FUNCTION@.
  | Function Meta (SpecMode, RecMode) [Type] [Formal]
             (Either (Structured ExpressionList) Process)
  -- | Declare a retyping abbreviation of a variable.
  | Retypes Meta AbbrevMode Type Variable
  -- | Declare a retyping abbreviation of an expression.
  | RetypesExpr Meta AbbrevMode Type Expression
  -- | A fake declaration of an unscoped name, such as a protocol tag.
  -- This allows 'SpecType' to be used to describe any identifier.
  | Unscoped Meta
  -- | A replicator (as in SEQ i = 0 FOR 6).  The scope of the replicator is
  -- the code that is replicated according to this replicator.
  | Rep Meta Replicator
  deriving (Show, Eq, Typeable, Data)

-- | Specification mode for @PROC@s and @FUNCTION@s.
-- This indicates whether a function is inlined by the compiler.
data SpecMode =
  PlainSpec | InlineSpec
  deriving (Show, Eq, Typeable, Data)

-- | Recursive mode for @PROC@s and @FUNCTION@s.
-- This indicates whether a function/proc can call itself, for which it must be
-- in scope during its own definition
data RecMode =
  PlainRec | Recursive
  deriving (Show, Eq, Typeable, Data)

-- | Formal parameters for @PROC@s and @FUNCTION@s.
data Formal =
  Formal AbbrevMode Type Name
  deriving (Show, Eq, Typeable, Data)

-- | Actual parameters for @PROC@s and @FUNCTION@s.
data Actual =
  -- | A variable used as a parameter.
  ActualVariable Variable
  -- | An expression used as a parameter.
  | ActualExpression Expression
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
  -- | Clears the given mobile variable; if the variable is currently NULL,
  -- destroy the contents and make it NULL.  If it is already NULL, do nothing.
  | ClearMobile Meta Variable
  | Skip Meta
  | Stop Meta
  | Seq Meta (Structured Process)
  | If Meta (Structured Choice)
  | Case Meta Expression (Structured Option)
  | While Meta Expression Process
  | Par Meta ParMode (Structured Process)
  -- | A @PROCESSOR@ process.
  -- The occam2.1 syntax says this is just a process, although it shouldn't be
  -- legal outside a @PLACED PAR@.
  | Processor Meta Expression Process
  | Alt Meta Bool (Structured Alternative)
  -- | Poisons the given channel(-end) (or barrier, in future)
  | InjectPoison Meta Variable
  | ProcCall Meta Name [Actual]
  -- | A call of a built-in @PROC@.
  -- This may go away in the future, since which @PROC@s are intrinsics depends
  -- on the backend.
  | IntrinsicProcCall Meta String [Actual]
  deriving (Show, Eq, Typeable, Data)

-- | The top level of the AST: a sequence of definitions.
type AST = Structured ()
