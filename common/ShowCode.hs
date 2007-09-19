{-# OPTIONS_GHC -fallow-incoherent-instances #-}
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

-- | A module with type-classes and functions for displaying code, dependent on the context.
-- Primarily, this means showing code as occam in error messages for the occam frontend, and Rain code for the Rain frontend.
module ShowCode (showCode, showOccam, showRain, formatCode, extCode) where 

import Control.Monad.State
import Data.Generics
import Data.List
import Text.PrettyPrint.HughesPJ
import Text.Regex
import qualified AST as A
import CompState

-- | A type-class that indicates that the data (AST item) is displayable as occam code.
class ShowOccam a where
  showOccam :: a -> String

-- | A type-class that indicates that the data (AST item) is displayable as Rain code.
class ShowRain a where
  showRain :: a -> String

-- | Shows the given code (AST item) as either occam or Rain code, depending on which frontend was selected
showCode :: (CSM m, ShowOccam a, ShowRain a) => a -> m String
showCode o
   = do st <- get
        return $ case csFrontend st of
                   FrontendOccam -> showOccam o
                   FrontendRain -> showRain o

-- | Some type hackery to allow formatCode to take a variable number of functions.
class CSM m => ShowCodeFormat a m | a -> m where
  chain :: [String] -> [m String] -> a

instance CSM m => ShowCodeFormat (m String) m where
  chain xs ys = (liftM concat) (sequence $ interleave (map return xs) (ys))
    where
      --Given [a,b,c] [1,2], produces [a,1,b,2,c] etc
      interleave :: [a] -> [a] -> [a]
      interleave xs [] = xs
      interleave [] ys = ys
      interleave (x:xs) (y:ys) = (x:y: (interleave xs ys))


instance (ShowOccam a, ShowRain a, ShowCodeFormat r m, CSM m) => ShowCodeFormat (a -> r) m where
  chain a x = (\y -> chain a (x ++ [showCode y]))
              

-- | Formats the given code as either occam or Rain code, depending on the frontend (using showCode).
-- Use like this:
-- dieC $ formatCode "Types do not match: % and %" ta tb
formatCode :: (CSM m,ShowCodeFormat r m) => String -> r
formatCode fmt = chain (splitRegex (mkRegex "%") fmt) []


--Type-class instances follow for ShowOccam and ShowRain:

instance ShowOccam A.Type where
  showOccam A.Bool = "BOOL"
  showOccam A.Byte = "BYTE"
  showOccam A.UInt16 = "UINT16"
  showOccam A.UInt32 = "UINT32"
  showOccam A.UInt64 = "UINT64"
  showOccam A.Int = "INT"
  showOccam A.Int8 = "INT8"
  showOccam A.Int16 = "INT16"
  showOccam A.Int32 = "INT32"
  showOccam A.Int64 = "INT64"
  showOccam A.Real32 = "REAL32"
  showOccam A.Real64 = "REAL64"
  showOccam (A.Array ds t)
      = concat [case d of
                  A.Dimension n -> "[" ++ show n ++ "]"
                  A.UnknownDimension -> "[]"
                | d <- ds] ++ showOccam t
  showOccam (A.UserDataType n) = A.nameName n ++ "{data type}"
  showOccam (A.Record n) = A.nameName n ++ "{record}"
  showOccam (A.UserProtocol n) = A.nameName n ++ "{protocol}"
  showOccam (A.Chan _ _ t) = "CHAN OF " ++ showOccam t
  showOccam (A.Counted ct et) = showOccam ct ++ "::" ++ showOccam et
  showOccam A.Any = "ANY"
  showOccam A.Timer = "TIMER"
  showOccam A.Time = "TIME"
  showOccam (A.Port t) = "PORT OF " ++ showOccam t


instance ShowRain A.Type where
  showRain A.Bool = "bool"
  showRain A.Byte = "uint8"
  showRain A.UInt16 = "uint16"
  showRain A.UInt32 = "uint32"
  showRain A.UInt64 = "uint64"
  showRain A.Int8 = "sint8"
  showRain A.Int16 = "sint16"
  showRain A.Int32 = "sint32"
  showRain A.Int64 = "int"
  showRain A.Int = "int"
  showRain (A.Chan dir attr t) 
    = case dir of
        A.DirUnknown -> "channel " ++ ao (A.caWritingShared attr) ++ "2" ++ ao (A.caReadingShared attr) ++ " " ++ showRain t
        A.DirInput -> (if A.caReadingShared attr then "shared" else "") ++ " ?" ++ showRain t
        A.DirOutput -> (if A.caWritingShared attr then "shared" else "") ++ " !" ++ showRain t
    where
      ao :: Bool -> String
      ao b = if b then "any" else "one"  
  showRain A.Time = "time"
  showRain x = "<invalid Rain type: " ++ show x ++ ">"

instance ShowOccam A.DyadicOp where
  showOccam A.Add = "+"
  showOccam A.Subtr = "-"
  showOccam A.Mul = "*"
  showOccam A.Div = "/"
  showOccam A.Rem = "REM"
  showOccam A.Plus = "PLUS"
  showOccam A.Minus = "MINUS"
  showOccam A.Times = "TIMES"
  showOccam A.BitAnd = "/\\"
  showOccam A.BitOr = "\\/"
  showOccam A.BitXor = "><"
  showOccam A.LeftShift = "<<"
  showOccam A.RightShift = ">>"
  showOccam A.And = "AND"
  showOccam A.Or = "OR"
  showOccam A.Eq = "="
  showOccam A.NotEq = "<>"
  showOccam A.Less = "<"
  showOccam A.More = ">"
  showOccam A.LessEq = "<="
  showOccam A.MoreEq = ">="
  showOccam A.After = "AFTER"


instance ShowRain A.DyadicOp where
  showRain A.Div = "/"
  showRain A.Rem = "%"
  showRain A.Plus = "+"
  showRain A.Minus = "-"
  showRain A.Times = "*"
  showRain A.And = "and"
  showRain A.Or = "or"
  showRain A.Eq = "=="
  showRain A.NotEq = "<>"
  showRain A.Less = "<"
  showRain A.More = ">"
  showRain A.LessEq = "<="
  showRain A.MoreEq = ">="
  showRain x = "<invalid Rain operator: " ++ show x ++ ">"

instance ShowOccam A.Variable where
  showOccam (A.Variable _ n) = show n
  showOccam (A.SubscriptedVariable _ s v) = showOccam v ++ "[" ++ show s ++ "]"
  showOccam (A.DirectedVariable _ A.DirUnknown v) = showOccam v
  showOccam (A.DirectedVariable _ A.DirInput v) = showOccam v ++ "?"
  showOccam (A.DirectedVariable _ A.DirOutput v) = showOccam v ++ "!"
  
instance ShowRain A.Variable where
  showRain (A.Variable _ n) = show n
  showRain (A.DirectedVariable _ A.DirInput v) = "?" ++ showRain v
  showRain (A.DirectedVariable _ A.DirOutput v) = "!" ++ showRain v
  showRain x = "<invalid Rain variable: " ++ show x ++ ">"

-- | Extends an existing (probably generic) function with cases for everything that has a specific ShowOccam and ShowRain instance
-- This is a bit of manual wiring.  Because we can't generically deduce whether or not 
-- a given Data item has a showRain/showOccam implementation (that I know of), I have 
-- had to add this function that has a line for each type that does have a 
-- ShowOccam/ShowRain implementation.  But since to add a type to the ShowOccam/ShowRain 
-- classes you have to provide a specific instance above anyway, I don't think that adding 
-- one more line while you're at it is too bad.
extCode :: Typeable b => (b -> Doc) -> (forall a. (ShowOccam a, ShowRain a) => a -> String) -> (b -> Doc)
extCode q f = q `extQ` (text . (f :: A.Type -> String))
                `extQ` (text . (f :: A.DyadicOp -> String))
                `extQ` (text . (f :: A.Variable -> String))
