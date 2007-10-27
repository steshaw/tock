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


-- TODO: This module is a mess.  It should probably use the writer monad instead of this +>> operator, and I've put
-- in some settings but some of them (such as realCode) are not wired up, and there's no easy way to set them
-- from outside this module.  Also, some things aren't quite right (such as replicated IFs), and due to the way
-- the occam parser works, a few SEQs get introduced if you parse a file then write it out again straight away.

-- So I'm committing this for the time being, but it really does need some work (and some tests, of course*) later on.

-- * My plan for testing was to take each of the cgtests, and parse it in to AST_A.  Then print AST_A using this
-- module, and feed it back in to the parser to get AST_B.  Then check if AST_A and AST_B are equal.

module ShowCode (showCode, showOccam, showRain, formatCode, extCode) where 

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ hiding (space, colon)
import Text.Regex

import qualified AST as A
import CompState

data ShowOccamState = ShowOccamState {
  indentLevel :: Int,  -- The indent level in spaces (add two for each indent)
  outerItem :: [String], -- What we are currently inside for Structureds, e.g. "IF" or "SEQ".  Use the head of the list
  useOriginalName :: Bool, -- Whether to use the original proc names
  realCode :: Bool, -- Whether to leave out all helpful hints (e.g. {protocol} on Protocols)
  originalNames :: Map.Map String String,
  suppressNextIndent :: Bool,
  -- Used to pass down variables for input modes, or for subscripts:
  tempItem :: OccamWriter String
}

--TODO use the Writer monad instead, with StateT
type OccamWriter a = State ShowOccamState a

initialShowOccamState :: Map.Map String String -> ShowOccamState
initialShowOccamState origNames = ShowOccamState {indentLevel = 0, outerItem = [], useOriginalName = True, realCode = True, 
                                                  originalNames = origNames,suppressNextIndent = False, tempItem = return ""}

showInputModeOccamM :: A.Variable -> A.InputMode -> OccamWriter String
showInputModeOccamM v im = do modify (\s -> s {tempItem = showOccamM v})
                              showOccamM im

showSubscriptOccamM :: ShowOccam a => a -> A.Subscript -> OccamWriter String
showSubscriptOccamM arr s = do modify (\s -> s {tempItem = showOccamM arr})
                               showOccamM s

suppressIndent :: OccamWriter String
suppressIndent = do st <- get
                    put (st {suppressNextIndent = True})
                    return ""

showOccamLine :: OccamWriter String -> OccamWriter String
showOccamLine s = do st <- get
                     (if (suppressNextIndent st)
                       then do put (st {suppressNextIndent = False})
                               return ""
                       else return (replicate (indentLevel st) ' ')
                      ) +>> s +>> return "\n"
                     

occamIndent :: OccamWriter String
occamIndent = do st <- get
                 put (st { indentLevel = (indentLevel st) + 2} )
                 return ""
occamOutdent :: OccamWriter String
occamOutdent = do st <- get
                  put (st { indentLevel = (indentLevel st) - 2} )
                  return ""

occamBlock :: OccamWriter String -> OccamWriter String
occamBlock s = occamIndent +>> s +>> occamOutdent

showName :: A.Name -> OccamWriter String
showName n = do st <- get
                return $ if useOriginalName st then Map.findWithDefault k k (originalNames st) else k
  where k = A.nameName n

helper :: String -> OccamWriter String
helper s = do st <- get
              return $ if (realCode st) then "" else s

currentContext :: OccamWriter String
currentContext = get >>= (return . head . outerItem)

pushContext :: String -> OccamWriter String
pushContext x = do st <- get
                   put (st {outerItem = (x:(outerItem st))})
                   return ""

beginStr :: String -> OccamWriter String
beginStr n = pushContext n >> occamIndent

endStr :: OccamWriter String
endStr = popContext >> occamOutdent

popContext :: OccamWriter String
popContext = do st <- get
                put (st {outerItem = tail (outerItem st)})
                return ""

doStr :: String -> OccamWriter String -> OccamWriter String
doStr n s = showOccamLine (return n) +>> (beginStr n) +>> s +>> endStr

--TODO remove this function?  Or at least rename it
showOccam :: ShowOccam a => a -> String
showOccam x = evalState (showOccamM x) (initialShowOccamState Map.empty)

bracket :: OccamWriter String -> OccamWriter String
bracket x = return "(" +>> x +>> return ")"
                
-- | A type-class that indicates that the data (AST item) is displayable as occam code.
class ShowOccam a where
--  showOccam :: a -> String
--  showOccam = const ""
  showOccamM :: a -> OccamWriter String

-- | A type-class that indicates that the data (AST item) is displayable as Rain code.
class ShowRain a where
  showRain :: a -> String

-- | Shows the given code (AST item) as either occam or Rain code, depending on which frontend was selected
showCode :: (CSM m, ShowOccam a, ShowRain a) => a -> m String
showCode o
   = do st <- get
        case csFrontend st of
          FrontendOccam -> do st <- get
                              return $ evalState (showOccamM o) (initialShowOccamState $ transformNames $ csNames st)
          FrontendRain -> return $ showRain o
 where
   transformNames :: Map.Map String A.NameDef -> Map.Map String String
   transformNames = Map.map A.ndOrigName

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
  showOccamM A.Bool = return "BOOL"
  showOccamM A.Byte = return "BYTE"
  showOccamM A.UInt16 = return "UINT16"
  showOccamM A.UInt32 = return "UINT32"
  showOccamM A.UInt64 = return "UINT64"
  showOccamM A.Int = return "INT"
  showOccamM A.Int8 = return "INT8"
  showOccamM A.Int16 = return "INT16"
  showOccamM A.Int32 = return "INT32"
  showOccamM A.Int64 = return "INT64"
  showOccamM A.Real32 = return "REAL32"
  showOccamM A.Real64 = return "REAL64"
  showOccamM A.Any = return "ANY"
  showOccamM A.Timer = return "TIMER"
  showOccamM A.Time = return "TIME"

  showOccamM (A.Mobile t) = return "MOBILE " +>> showOccamM t
  showOccamM (A.Array ds t)
      = (return $ concat [case d of
                  A.Dimension n -> "[" ++ show n ++ "]"
                  A.UnknownDimension -> "[]"
                | d <- ds]) +>> showOccamM t
  showOccamM (A.Chan _ _ t) = return "CHAN OF " +>> showOccamM t
  showOccamM (A.Counted ct et) = showOccamM ct +>> return "::" +>> showOccamM et
  showOccamM (A.Port t) = return "PORT OF " +>> showOccamM t
  showOccamM (A.UserDataType n) = showName n +>> helper "{data type}"
  showOccamM (A.Record n) = showName n +>> helper "{record}"
  showOccamM (A.UserProtocol n) = showName n +>> helper "{protocol}"
  showOccamM (A.List t) = return "LIST " +>> showOccamM t

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
  -- Mobility is not explicit in Rain:
  showRain (A.Mobile t) = showRain t
  showRain (A.List t) = "[" ++ showRain t ++ "]"
  showRain x = "<invalid Rain type: " ++ show x ++ ">"

instance ShowOccam A.DyadicOp where
  showOccamM A.Add = return "+"
  showOccamM A.Subtr = return "-"
  showOccamM A.Mul = return "*"
  showOccamM A.Div = return "/"
  showOccamM A.Rem = return "REM"
  showOccamM A.Plus = return "PLUS"
  showOccamM A.Minus = return "MINUS"
  showOccamM A.Times = return "TIMES"
  showOccamM A.BitAnd = return "/\\"
  showOccamM A.BitOr = return "\\/"
  showOccamM A.BitXor = return "><"
  showOccamM A.LeftShift = return "<<"
  showOccamM A.RightShift = return ">>"
  showOccamM A.And = return "AND"
  showOccamM A.Or = return "OR"
  showOccamM A.Eq = return "="
  showOccamM A.NotEq = return "<>"
  showOccamM A.Less = return "<"
  showOccamM A.More = return ">"
  showOccamM A.LessEq = return "<="
  showOccamM A.MoreEq = return ">="
  showOccamM A.After = return "AFTER"


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

instance ShowOccam A.MonadicOp where
  showOccamM A.MonadicSubtr = return "-"
  showOccamM A.MonadicMinus = return "MINUS"
  showOccamM A.MonadicBitNot = return "~"
  showOccamM A.MonadicNot = return "NOT"

instance ShowOccam A.Variable where
  showOccamM (A.Variable _ n) = showName n
  showOccamM (A.SubscriptedVariable _ s v) = showSubscriptOccamM v s
  showOccamM (A.DirectedVariable _ A.DirUnknown v) = showOccamM v
  showOccamM (A.DirectedVariable _ A.DirInput v) = showOccamM v +>> return "?"
  showOccamM (A.DirectedVariable _ A.DirOutput v) = showOccamM v +>> return "!"
  
instance ShowRain A.Variable where
  showRain (A.Variable _ n) = show n
  showRain (A.DirectedVariable _ A.DirInput v) = "?" ++ showRain v
  showRain (A.DirectedVariable _ A.DirOutput v) = "!" ++ showRain v
  showRain x = "<invalid Rain variable: " ++ show x ++ ">"

instance ShowOccam A.ArrayElem where
  showOccamM (A.ArrayElemArray elems) = return "[" +>> showWithCommas elems +>> return "]"
  showOccamM (A.ArrayElemExpr e) = showOccamM e

instance ShowOccam A.LiteralRepr where
  showOccamM (A.RealLiteral _ s) = return s
  showOccamM (A.IntLiteral _ s) = return s
  showOccamM (A.HexLiteral _ s) = return ("#" ++ s)
  showOccamM (A.ByteLiteral _ s) = return ("'" ++ s ++ "'")
  showOccamM (A.ArrayLiteral _ elems) = return "[" +>> showWithCommas elems +>> return "]"  
  --TODO record literals

instance ShowOccam A.Subscript where
  showOccamM (A.Subscript _ e) = getTempItem +>> return "[" +>> showOccamM e +>> return "]"
  showOccamM (A.SubscriptField _ n) = getTempItem +>> return "[" +>> showName n +>> return "]"
  showOccamM (A.SubscriptFromFor _ start count)
    = return "[" +>> getTempItem +>> return " FROM " +>> showOccamM start +>> return " FOR " +>> showOccamM count +>> return "]"
  showOccamM (A.SubscriptFor _ count)
    = return "[" +>> getTempItem +>> return " FOR " +>> showOccamM count +>> return "]"
  showOccamM (A.SubscriptFrom _ start)
    = return "[" +>> getTempItem +>> return " FROM " +>> showOccamM start +>> return "]"        
  

convOrSpace :: A.ConversionMode -> OccamWriter String
convOrSpace A.DefaultConversion = space
convOrSpace A.Round = return " ROUND "
convOrSpace A.Trunc = return " TRUNC "

instance ShowOccam A.Expression where
  showOccamM (A.Monadic _ op e) = bracket $ showOccamM op +>> space +>> showOccamM e
  showOccamM (A.Dyadic _ op lhs rhs) = bracket $ showOccamM lhs +>> space +>> showOccamM op +>> space +>> showOccamM rhs
  showOccamM (A.MostPos _ t) = bracket $ return "MOSTPOS " +>> showOccamM t
  showOccamM (A.MostNeg _ t) = bracket $ return "MOSTNEG " +>> showOccamM t
  showOccamM (A.SizeType _ t) = bracket $ return "SIZE " +>> showOccamM t
  showOccamM (A.SizeExpr _ e) = bracket $ return "SIZE " +>> showOccamM e
  showOccamM (A.SizeVariable _ v) = bracket $ return "SIZE " +>> showOccamM v
  showOccamM (A.Conversion _ cm t e) = bracket $ showOccamM t +>> convOrSpace cm +>> showOccamM e
  showOccamM (A.ExprVariable _ v) = showOccamM v
  showOccamM (A.Literal _ _ lit) = showOccamM lit
  showOccamM (A.True _) = return "TRUE"
  showOccamM (A.False _) = return "FALSE"
  showOccamM (A.FunctionCall _ n es) = showName n +>> return "(" +>> showWithCommas es +>> return ")"
  showOccamM (A.SubscriptedExpr _ s e) = showSubscriptOccamM e s
  showOccamM (A.BytesInExpr _ e) = bracket $ return "BYTESIN " +>> showOccamM e
  showOccamM (A.BytesInType _ t) = bracket $ return "BYTESIN " +>> showOccamM t
  showOccamM (A.OffsetOf _ t n) = return "OFFSETOF(" +>> showOccamM t +>> return " , " +>> showName n +>> return ")"
  --TODO exprconstr

instance ShowOccam A.Formal where
  showOccamM (A.Formal am t n) = (maybeVal am)
                                 +>> (showOccamM t)
                                 +>> space
                                 +>> (showName n)
                  
space :: OccamWriter String
space = return " "

colon :: OccamWriter String
colon = return ":"

maybeVal :: A.AbbrevMode -> OccamWriter String
maybeVal am = return $ if (am == A.ValAbbrev) then "VAL " else ""

instance ShowOccam A.Specification where
  -- TODO add specmode to the output
  showOccamM (A.Specification _ n (A.Proc _ sm params body))
    = do n' <- showName n
         params' <- showAll (intersperse (return ",") $ map showOccamM params)
         --TODO use the occamdoc setting
         showOccamLine (return $ "PROC " ++ n' ++ "(" ++ params' ++ ")") +>> occamIndent +>> showOccamM body +>> occamOutdent +>> showOccamLine (return ":")
  showOccamM (A.Specification _ n (A.Declaration _ t Nothing))
    = showOccamLine $ showOccamM t +>> space +>> showName n +>> colon
  showOccamM (A.Specification _ n (A.Declaration _ t (Just e)))
    = showOccamLine $ return "INITIAL " +>> showOccamM t +>> space +>> showName n +>> return " IS " +>> showOccamM e +>> colon
  showOccamM (A.Specification _ n (A.Is _ am t v))
    = showOccamLine $ (maybeVal am) +>> showOccamM t +>> space +>> showName n +>> return " IS " +>> showOccamM v +>> colon
  showOccamM (A.Specification _ n (A.IsExpr _ am t e))
    = showOccamLine $ (maybeVal am) +>> showOccamM t +>> space +>> showName n +>> return " IS " +>> showOccamM e +>> colon
  showOccamM (A.Specification _ n (A.IsChannelArray _ t vs))
    = showOccamLine $ showOccamM t +>> space +>> showName n +>> return " IS [" +>> showWithCommas vs +>> return "]:"
  showOccamM (A.Specification _ n (A.DataType _ t))
    = showOccamLine $ return "DATA TYPE " +>> showName n +>> return " IS " +>> showOccamM t +>> colon
  showOccamM (A.Specification _ n (A.RecordType _ packed fields))
    = (showOccamLine $ return "DATA TYPE " +>> showName n)
      +>> occamIndent
      +>> (showOccamLine $ return (if packed then "PACKED RECORD" else "RECORD"))
      +>> occamIndent
      +>> (showAll (map (\(n,t) -> showOccamLine $ showOccamM t +>> space +>> showName n +>> colon) fields))
      +>> occamOutdent
      +>> occamOutdent
      +>> (showOccamLine colon)
  --TODO use the specmode
  showOccamM (A.Specification _ n (A.Function _ sm retTypes params el@(A.OnlyEL {})))
    = showOccamLine $
        showWithCommas retTypes +>> (return " FUNCTION ") +>> showName n +>> return "(" +>> showWithCommas params +>> return ")"
        +>> return " IS " +>> showOccamM el +>> colon
  showOccamM (A.Specification _ n (A.Function _ sm retTypes params body))
    = (showOccamLine $ showWithCommas retTypes +>> (return " FUNCTION ") +>> showName n +>> return "(" +>> showWithCommas params +>> return ")")
      +>> occamIndent
      +>> showOccamM body
      +>> occamOutdent
      +>> showOccamLine colon
  showOccamM (A.Specification _ n (A.Protocol _ ts))
    = showOccamLine $ return "PROTOCOL " +>> showName n +>> return " IS " +>> showWithSemis ts +>> colon
  showOccamM (A.Specification _ n (A.ProtocolCase _ nts))
    = (showOccamLine $ return "PROTOCOL " +>> showName n) +>> occamBlock
        (showOccamLine (return "CASE") +>> occamBlock
          (showAll $ map (showOccamLine . showProtocolItem) nts)
      ) +>> colon
  showOccamM (A.Specification _ n (A.Retypes _ am t v))
    = showOccamLine $ maybeVal am +>> showOccamM t +>> space +>> showName n +>> return " RETYPES " +>> showOccamM v +>> colon
  showOccamM (A.Specification _ n (A.RetypesExpr _ am t e))
    = showOccamLine $ maybeVal am +>> showOccamM t +>> space +>> showName n +>> return " RETYPES " +>> showOccamM e +>> colon
  
showProtocolItem :: (A.Name, [A.Type]) -> OccamWriter String
showProtocolItem (n,ts) = showAll $ intersperse (return " ; ") $ [showName n] ++ (map showOccamM ts)
  
instance ShowOccam A.Variant where
  showOccamM (A.Variant _ n iis p)
    = (showOccamLine (showAll $ intersperse (return " ; ") $ [showName n] ++ (map showOccamM iis)))
      +>> occamIndent +>> showOccamM p +>> occamOutdent
           
instance ShowOccam A.Actual where
  showOccamM (A.ActualVariable _ _ v) = showOccamM v
  showOccamM (A.ActualExpression _ e) = showOccamM e
  
instance ShowOccam A.OutputItem where
  showOccamM (A.OutExpression _ e) = showOccamM e
  showOccamM (A.OutCounted _ ce ae) = showOccamM ce +>> return " :: " +>> showOccamM ae
  
getTempItem :: OccamWriter String
getTempItem = get >>= tempItem

instance ShowOccam A.InputItem where 
  showOccamM (A.InVariable _ v) = showOccamM v
  showOccamM (A.InCounted _ cv av) = showOccamM cv +>> return " :: " +>> showOccamM av
  
instance ShowOccam A.InputMode where
  showOccamM (A.InputSimple _ iis)
    = showOccamLine $ getTempItem +>> return " ? " +>> (showWithSemis iis)
  showOccamM (A.InputCase _ str)
    = (showOccamLine $ getTempItem +>> return " ? CASE") +>> occamIndent +>> showOccamM str +>> occamOutdent
  showOccamM (A.InputTimerRead _ ii)
    = showOccamLine $ getTempItem +>> return " ? " +>> showOccamM ii
  showOccamM (A.InputTimerAfter _ e)
    = showOccamLine $ getTempItem +>> return " ? AFTER " +>> showOccamM e
  
  
instance ShowOccam A.Alternative where
  showOccamM (A.Alternative _ v im p) = showInputModeOccamM v im +>> occamIndent +>> showOccamM p +>> occamOutdent
  showOccamM (A.AlternativeCond _ e v im p) = showOccamM e +>> return " & " +>> suppressIndent +>> showOccamM (A.Alternative undefined v im p)
  
instance ShowOccam A.Replicator where
  showOccamM (A.For _ n start count) = return " " +>> showName n +>> return " = " +>> showOccamM start +>> return " FOR " +>> showOccamM count
  showOccamM (A.ForEach _ n e) = return " " +>> showName n +>> return " IN " +>> showOccamM e

instance ShowOccam A.Choice where
  showOccamM (A.Choice _ e p) = showOccamLine (showOccamM e) +>> occamBlock (showOccamM p)

instance ShowOccam A.Option where
  showOccamM (A.Option _ es p) = showOccamLine (showAll $ intersperse (return " , ") $ map showOccamM es) +>> occamBlock (showOccamM p)
  showOccamM (A.Else _ p) = showOccamLine (return "ELSE") +>> occamBlock (showOccamM p)

instance ShowOccam A.Structured where
  showOccamM (A.Spec _ spec str) = showOccamM spec +>> showOccamM str
  showOccamM (A.Rep _ rep str)
    = do item <- currentContext
         (showOccamLine (return (item ++ " ") +>> showOccamM rep)) +>> occamIndent +>> showOccamM str +>> occamOutdent
  showOccamM (A.OnlyP _ p) = showOccamM p
  showOccamM (A.OnlyEL _ el) = showOccamM el
  showOccamM (A.OnlyA _ a) = showOccamM a
  showOccamM (A.OnlyV _ v) = showOccamM v
  showOccamM (A.OnlyC _ c) = showOccamM c
  showOccamM (A.OnlyO _ o) = showOccamM o
  showOccamM (A.Several _ ss) = showAll $ map showOccamM ss
  showOccamM (A.ProcThen _ p str) = showOccamLine (return "VALOF") +>> occamBlock (showOccamM p +>> showOccamLine (return "RESULT " +>> showOccamM str))

showWithCommas :: ShowOccam a => [a] -> OccamWriter String
showWithCommas ss = showAll $ intersperse (return " , ") $ map showOccamM ss

showWithSemis :: ShowOccam a => [a] -> OccamWriter String
showWithSemis ss = showAll $ intersperse (return " ; ") $ map showOccamM ss

instance ShowOccam A.ExpressionList where
  showOccamM (A.ExpressionList _ es) = showWithCommas es
  --TODO functioncalllist

outer :: String -> A.Structured -> OccamWriter String
outer keyword (A.Rep _ rep str) = showOccamLine (return keyword +>> showOccamM rep) +>> beginStr keyword +>> showOccamM str +>> endStr
outer keyword str = doStr keyword (showOccamM str)

instance ShowOccam A.Process where
  showOccamM (A.Assign _ vs el) = showOccamLine (showWithCommas vs +>> return ":=" +>> showOccamM el)
  showOccamM (A.Skip _) = showOccamLine $ return "SKIP"
  showOccamM (A.Stop _) = showOccamLine $ return "STOP" 
  showOccamM (A.Input _ v im) = showInputModeOccamM v im
  showOccamM (A.Output _ v ois) = showOccamLine $ showOccamM v +>> return " ! " +>> (showWithSemis ois)
  showOccamM (A.OutputCase _ v n ois) = showOccamLine $ showOccamM v +>> return " ! " +>> 
    (showAll $ intersperse (return " ; ") $ [showName n] ++ (map showOccamM ois))
  --TODO gettime and wait ?
  
  --TODO proccall
  showOccamM (A.ProcCall _ n params) = showOccamLine $ showName n +>> return " ( " +>> showWithCommas params +>> return " ) "
  showOccamM (A.While _ e p) = (showOccamLine $ return "WHILE " +>> showOccamM e) +>> occamIndent +>> showOccamM p +>> occamOutdent
  showOccamM (A.Case _ e s) = (showOccamLine $ return "CASE " +>> showOccamM e) +>> occamBlock (showOccamM s)
  showOccamM (A.If _ str) = outer "IF" str
  showOccamM (A.Alt _ False str) = outer "ALT" str
  showOccamM (A.Alt _ True str) = outer "PRI ALT" str
  showOccamM (A.Seq _ str) = outer "SEQ" str
  showOccamM (A.Par _ A.PlainPar str) = outer "PAR" str
  showOccamM (A.Par _ A.PriPar str) = outer "PRI PAR" str
  showOccamM (A.Par _ A.PlacedPar str) = outer "PLACED PAR" str
--  showOccamM _x = return $ "#error unimplemented" ++ show _x

--TEMP:
instance ShowRain a where
  showRain = const ""

-- | Extends an existing (probably generic) function with cases for everything that has a specific ShowOccam and ShowRain instance
-- This is a bit of manual wiring.  Because we can't generically deduce whether or not 
-- a given Data item has a showRain\/showOccam implementation (that I know of), I have 
-- had to add this function that has a line for each type that does have a 
-- ShowOccam\/ShowRain implementation.  But since to add a type to the ShowOccam\/ShowRain 
-- classes you have to provide a specific instance above anyway, I don't think that adding 
-- one more line while you're at it is too bad.
extCode :: Typeable b => (b -> Doc) -> (forall a. (ShowOccam a, ShowRain a) => a -> String) -> (b -> Doc)
extCode q f = q 
                `extQ` (text . (f :: A.DyadicOp -> String))
                `extQ` (text . (f :: A.Expression -> String))
                `extQ` (text . (f :: A.ExpressionList -> String))
                `extQ` (text . (f :: A.Formal -> String))
                `extQ` (text . (f :: A.MonadicOp -> String))
                `extQ` (text . (f :: A.Process -> String))
                `extQ` (text . (f :: A.Replicator -> String))
                `extQ` (text . (f :: A.Specification -> String))
                `extQ` (text . (f :: A.Structured -> String))
                `extQ` (text . (f :: A.Type -> String))
                `extQ` (text . (f :: A.Variable -> String))

(+>>) :: State s [a] -> State s [a] -> State s [a]
(+>>) x y = do x' <- x
               y' <- y
               return (x' ++ y')

showAll :: [State s [a]] -> State s [a]
showAll = foldl (+>>) (return [])
