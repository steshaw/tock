-- | Data types for occam abstract syntax.
-- This is intended to be imported qualified as A.
module AST where

import Data.Generics

import Metadata

data NameType =
  ChannelName | DataTypeName | FunctionName | FieldName | PortName
  | ProcName | ProtocolName | RecordName | TagName | TimerName | VariableName
  deriving (Show, Eq, Typeable, Data)

-- | A name structure for variable names in the AST.
data Name = Name {
    -- | The meta tag that indicates the location of this instance (use) of the name 
    nameMeta :: Meta,
    -- | The type of the thing referred to by this Name
    nameType :: NameType,
    -- | The resolved name
    nameName :: String
  }
  deriving (Typeable, Data)

instance Show Name where
  show n = show $ nameName n

instance Eq Name where
  (==) a b = nameName a == nameName b

-- | A structure for holding information about the definition of a name
data NameDef = NameDef {
    -- | The meta tag that indicates the location of the definition
    ndMeta :: Meta,
    -- | The resolved name
    ndName :: String,
    -- | The original (raw, unresolved) name
    ndOrigName :: String,
    -- | The type of the thing being named
    ndNameType :: NameType,
    -- | The specification type (e.g. declaration, IS, RETYPES)
    ndType :: SpecType,
    -- | The abbreviation mode (e.g. VAL abbreviation)
    ndAbbrevMode :: AbbrevMode,
    -- | The placement of the variable (e.g. PLACE AT)
    ndPlacement :: Placement
  }
  deriving (Show, Eq, Typeable, Data)

data Type =
  Bool
  | Byte
  | Int | Int16 | Int32 | Int64
  | Real32 | Real64
  -- | For N-dimensional arrays, the [Dimension] list will be of length N
  | Array [Dimension] Type
  | UserDataType Name
  | Record Name
  | UserProtocol Name
  | Chan Type
  | Counted Type Type
  | Any
  | Timer
  | Port Type
  deriving (Eq, Typeable, Data)

instance Show Type where
  show Bool = "BOOL"
  show Byte = "BYTE"
  show Int = "INT"
  show Int16 = "INT16"
  show Int32 = "INT32"
  show Int64 = "INT64"
  show Real32 = "REAL32"
  show Real64 = "REAL64"
  show (Array ds t)
      = concat [case d of
                  Dimension n -> "[" ++ show n ++ "]"
                  UnknownDimension -> "[]"
                | d <- ds] ++ show t
  show (UserDataType n) = nameName n ++ "{data type}"
  show (Record n) = nameName n ++ "{record}"
  show (UserProtocol n) = nameName n ++ "{protocol}"
  show (Chan t) = "CHAN OF " ++ show t
  show (Counted ct et) = show ct ++ "::" ++ show et
  show Any = "ANY"
  show Timer = "TIMER"
  show (Port t) = "PORT OF " ++ show t

-- | occam arrays are permitted to have empty unknown dimensions, hence Dimension is not simply an integer
data Dimension =
  Dimension Int
  | UnknownDimension
  deriving (Show, Eq, Typeable, Data)

data Placement =
  Unplaced
  | PlaceInWorkspace
  | PlaceInVecspace
  | PlaceAt Expression
  deriving (Show, Eq, Typeable, Data)

data ConversionMode =
  DefaultConversion
  | Round
  | Trunc
  deriving (Show, Eq, Typeable, Data)

-- | Various different subscripts that can be used in occams
data Subscript =
  -- | A single array subscript
  Subscript Meta Expression
  -- | A subscript that names a field of a record type
  | SubscriptField Meta Name
  -- | A subscript pair that creates an array slice.  
  -- The first Expression is the FROM; the initial value to begin at, inclusive
  -- The second Expression is the FOR; the count of items to include in the slice.
  | SubscriptFromFor Meta Expression Expression
  -- | Like SubscriptFromFor, but without a FOR; it goes to the end of the array
  | SubscriptFrom Meta Expression
  -- | Like SubscriptFromFor, but without a FROM; it starts from the beginning of the array
  | SubscriptFor Meta Expression
  deriving (Show, Eq, Typeable, Data)

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

-- | A variable can either be plain (e.g. "c") or subscripted (e.g. "c[0]" or "person[name]"
data Variable =
  Variable Meta Name
  | SubscriptedVariable Meta Subscript Variable
  deriving (Show, Eq, Typeable, Data)

data Expression =
  -- | A monadic/unary operator
  Monadic Meta MonadicOp Expression
  -- | A dyadic/binary operator
  | Dyadic Meta DyadicOp Expression Expression
  -- | The most positive value of a given type
  | MostPos Meta Type
  -- | The most negative value of a given type
  | MostNeg Meta Type
  -- | The size of a given array type, see SizeExpr
  | SizeType Meta Type
  -- | The size of a given array in number of sub-components. 
  -- As the occam 2 reference manual explains, given [8][4]INT a:, SIZE a is 8 and SIZE a[0] is 4
  | SizeExpr Meta Expression
  -- | See SizeExpr
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
  deriving (Show, Eq, Typeable, Data)

data ExpressionList =
  FunctionCallList Meta Name [Expression]
  | ExpressionList Meta [Expression]
  deriving (Show, Eq, Typeable, Data)

data MonadicOp =
  MonadicSubtr
  | MonadicBitNot
  | MonadicNot
  deriving (Show, Eq, Typeable, Data)

data DyadicOp =
  Add | Subtr | Mul | Div | Rem
  | Plus | Minus | Times
  | BitAnd | BitOr | BitXor
  | LeftShift | RightShift
  | And | Or
  | Eq | NotEq | Less | More | LessEq | MoreEq
  | After
  deriving (Show, Eq, Typeable, Data)

-- | Input items in occam can either be counted arrays, or single variables
data InputItem =
  -- | The first variable is the count, the second is the array
  InCounted Meta Variable Variable
  | InVariable Meta Variable
  deriving (Show, Eq, Typeable, Data)

-- | Output items in occam can either be counted arrays, or single variables
data OutputItem =
  -- | The first expression is the count, the second is the array
  OutCounted Meta Expression Expression
  | OutExpression Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | The Name names the replicator index, the first expression is the base and the second expression is the FOR
data Replicator = For Meta Name Expression Expression
  deriving (Show, Eq, Typeable, Data)

-- | A choice in an IF statement
data Choice = Choice Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

-- | A guard in an ALT
data Alternative =
  -- | A plain guard.  The channel/timer is the Variable, and the destination (or AFTER clause) is inside the InputMode.
  -- The process is the body of the guard
  Alternative Meta Variable InputMode Process
  -- | A conditional guard.  The Expression is the pre-condition, everything else is as Alternative above
  | AlternativeCond Meta Expression Variable InputMode Process
  -- | A skip guard (always ready).  The Expression is the pre-condition.
  | AlternativeSkip Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

-- | An option in a CASE statement
data Option =
  -- | A single CASE option can have multiple expressions to match against
  Option Meta [Expression] Process
  -- | The else guard is picked if no other options match.  It does not have to be the last option.
  | Else Meta Process
  deriving (Show, Eq, Typeable, Data)

-- | An option in an "? CASE" (input-case) statement
-- The name is the protocol tag, followed by zero or more input items, followed by the process to be
-- executed if that option is matched
data Variant = Variant Meta Name [InputItem] Process
  deriving (Show, Eq, Typeable, Data)

-- |This represents something that can contain local replicators and specifications.
-- (This ought to be a parametric type, "Structured Variant" etc., but doing so
-- makes using generic functions across it hard.)
data Structured =
  Rep Meta Replicator Structured
  | Spec Meta Specification Structured
  | ProcThen Meta Process Structured
  | OnlyV Meta Variant                  -- ^ Variant (CASE) input process
  | OnlyC Meta Choice                   -- ^ IF process
  | OnlyO Meta Option                   -- ^ CASE process
  | OnlyA Meta Alternative              -- ^ ALT process
  | OnlyP Meta Process                  -- ^ SEQ, PAR
  | OnlyEL Meta ExpressionList          -- ^ VALOF
  | Several Meta [Structured]
  deriving (Show, Eq, Typeable, Data)

data InputMode =
  InputSimple Meta [InputItem]
  | InputCase Meta Structured
  | InputTimerRead Meta InputItem
  | InputTimerAfter Meta Expression
  deriving (Show, Eq, Typeable, Data)

-- | Abbreviation mode.
data AbbrevMode =
  -- | No abbreviation
  Original
  -- | An abbreviation (by reference)
  | Abbrev
  -- | An abbreviation (by value)
  | ValAbbrev
  deriving (Show, Eq, Typeable, Data)

-- | Used for introducing specifications (process/function declarations, variables, type definitions, abbreviations, etc)
data Specification =
  Specification Meta Name SpecType
  deriving (Show, Eq, Typeable, Data)

-- | Used when declaring a Specification
data SpecType =
  -- | Places a variable at a given memory location
  Place Meta Expression
  -- | Declares a variable of the given type
  | Declaration Meta Type
  -- | Declares an abbreviation
  | Is Meta AbbrevMode Type Variable
  -- | Declares a constant to be a particular expression
  | IsExpr Meta AbbrevMode Type Expression
  -- | Declares an array that abbreviates some channels (the list of Variable).
  | IsChannelArray Meta Type [Variable]
  -- | Declares a data type (like a typedef)
  | DataType Meta Type
  -- | Declares a new record type.  The Bool is True if the record is PACKED, False otherwise.  
  --  The list of (Name,Type) are the members of the record
  | RecordType Meta Bool [(Name, Type)]
  -- | Declares a simple (sequential) protocol that has the type-list in order as its data items.
  | Protocol Meta [Type]
  -- | Declares a protocol with choice.  Each (Name, [Type]) is a tag name, 
  -- followed by various data items (as per simple sequential protocols).
  | ProtocolCase Meta [(Name, [Type])]
  -- | Declares a procedure.  SpecMode is inline or plain.
  -- The list of Formal are the parameters to the procedure, and the Process
  -- is the actual body of the procedure.
  | Proc Meta SpecMode [Formal] Process
  -- | Declares a function.  Much the same as Proc, but the list of Type is the return type.
  | Function Meta SpecMode [Type] [Formal] Structured
  -- | Declares a retyping abbreviation.  Type is the new type.  Variable is the variable being retyped
  | Retypes Meta AbbrevMode Type Variable
  -- | Declares a retyping abbreviation.  Type is the new type.  Expression is the expression being retyped
  | RetypesExpr Meta AbbrevMode Type Expression
  deriving (Show, Eq, Typeable, Data)

data SpecMode =
  PlainSpec | InlineSpec
  deriving (Show, Eq, Typeable, Data)

-- | Formal parameters, as in procedure parameter definitions
data Formal =
  Formal AbbrevMode Type Name
  deriving (Show, Eq, Typeable, Data)

-- | Actual parameters to calls of functions/procedures
data Actual =
  -- | A variable used as a parameter.
  -- I believe AbbrevMode here is included only for convenience - and the same for Type
  ActualVariable AbbrevMode Type Variable
  -- | An expression used as a parameter
  | ActualExpression Type Expression
  deriving (Show, Eq, Typeable, Data)

data ParMode =
  PlainPar | PriPar | PlacedPar
  deriving (Show, Eq, Typeable, Data)

data Process =
  Assign Meta [Variable] ExpressionList
  | Input Meta Variable InputMode
  | Output Meta Variable [OutputItem]
  | OutputCase Meta Variable Name [OutputItem]
  | Skip Meta
  | Stop Meta
  | Main Meta
  | Seq Meta Structured
  | If Meta Structured
  | Case Meta Expression Structured
  | While Meta Expression Process
  | Par Meta ParMode Structured
  | Processor Meta Expression Process
  | Alt Meta Bool Structured
  | ProcCall Meta Name [Actual]
  | IntrinsicProcCall Meta String [Actual]
  deriving (Show, Eq, Typeable, Data)

