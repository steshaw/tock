-- | Data types for occam abstract syntax.
-- This is intended to be imported qualified as A.
module AST where

import Data.Generics

import Metadata

data NameType =
  ChannelName | DataTypeName | FunctionName | FieldName | PortName
  | ProcName | ProtocolName | TagName | TimerName | VariableName
  deriving (Show, Eq, Typeable, Data)

data Name = Name {
    nameMeta :: Meta,
    nameType :: NameType,
    nameName :: String
  }
  deriving (Typeable, Data)

instance Show Name where
  show n = show $ nameName n

instance Eq Name where
  (==) a b = nameName a == nameName b

data NameDef = NameDef {
    ndMeta :: Meta,
    ndName :: String,
    ndOrigName :: String,
    ndNameType :: NameType,
    ndType :: SpecType,
    ndAbbrevMode :: AbbrevMode,
    ndPlacement :: Placement
  }
  deriving (Show, Eq, Typeable, Data)

data Type =
  Bool
  | Byte
  | Int | Int16 | Int32 | Int64
  | Real32 | Real64
  | Array [Dimension] Type
  | UserDataType Name
  | UserProtocol Name
  | Chan Type
  | Counted Type Type
  | Any
  | Timer
  | Port Type
  deriving (Show, Eq, Typeable, Data)

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

data Subscript =
  Subscript Meta Expression
  | SubscriptField Meta Name
  | SubscriptFromFor Meta Expression Expression
  | SubscriptFrom Meta Expression
  | SubscriptFor Meta Expression
  deriving (Show, Eq, Typeable, Data)

data LiteralRepr =
  RealLiteral Meta String
  | IntLiteral Meta String
  | HexLiteral Meta String
  | ByteLiteral Meta String
  | ArrayLiteral Meta [ArrayElem]
  deriving (Show, Eq, Typeable, Data)

-- | An item inside an array literal -- which might be an expression, or might
-- be a nested array. (occam multidimensional arrays are not arrays of arrays,
-- which is why we can't just use nested Literals.)
data ArrayElem =
  ArrayElemArray [ArrayElem]
  | ArrayElemExpr Expression
  deriving (Show, Eq, Typeable, Data)

data Variable =
  Variable Meta Name
  | SubscriptedVariable Meta Subscript Variable
  deriving (Show, Eq, Typeable, Data)

data Expression =
  Monadic Meta MonadicOp Expression
  | Dyadic Meta DyadicOp Expression Expression
  | MostPos Meta Type
  | MostNeg Meta Type
  | SizeType Meta Type
  | SizeExpr Meta Expression
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

data InputItem =
  InCounted Meta Variable Variable
  | InVariable Meta Variable
  deriving (Show, Eq, Typeable, Data)

data OutputItem =
  OutCounted Meta Expression Expression
  | OutExpression Meta Expression
  deriving (Show, Eq, Typeable, Data)

data Replicator = For Meta Name Expression Expression
  deriving (Show, Eq, Typeable, Data)

data Choice = Choice Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

data Alternative =
  Alternative Meta Variable InputMode Process
  | AlternativeCond Meta Expression Variable InputMode Process
  | AlternativeSkip Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

data Option =
  Option Meta [Expression] Process
  | Else Meta Process
  deriving (Show, Eq, Typeable, Data)

data Variant = Variant Meta Name [InputItem] Process
  deriving (Show, Eq, Typeable, Data)

-- This represents something that can contain local replicators and specifications.
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
  | InputAfter Meta Expression
  deriving (Show, Eq, Typeable, Data)

data AbbrevMode =
  Original
  | Abbrev
  | ValAbbrev
  deriving (Show, Eq, Typeable, Data)

data Specification =
  Specification Meta Name SpecType
  deriving (Show, Eq, Typeable, Data)

data SpecType =
  Place Meta Expression
  | Declaration Meta Type
  | Is Meta AbbrevMode Type Variable
  | IsExpr Meta AbbrevMode Type Expression
  | IsChannelArray Meta Type [Variable]
  | DataType Meta Type
  | DataTypeRecord Meta Bool [(Name, Type)]
  | Protocol Meta [Type]
  | ProtocolCase Meta [(Name, [Type])]
  | Proc Meta SpecMode [Formal] Process
  | Function Meta SpecMode [Type] [Formal] Structured
  | Retypes Meta AbbrevMode Type Variable
  | RetypesExpr Meta AbbrevMode Type Expression
  deriving (Show, Eq, Typeable, Data)

data SpecMode =
  PlainSpec | InlineSpec
  deriving (Show, Eq, Typeable, Data)

data Formal =
  Formal AbbrevMode Type Name
  deriving (Show, Eq, Typeable, Data)

data Actual =
  ActualVariable AbbrevMode Type Variable
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

