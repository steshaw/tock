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

-- My plan for testing was to take each of the cgtests, and parse it in to AST_A.  Then print AST_A using this
-- module, and feed it back in to the parser to get AST_B.  Then check if AST_A and AST_B are equal.

module ShowCode (showCode, ShowOccam(..), showOccam, ShowRain(..), showRain, formatCode, extCode) where 

import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ hiding (space, colon)
import Text.Regex

import qualified AST as A
import CompState hiding (CSM) -- everything here is read-only
import Utils

data ShowCodeState = ShowCodeState {
  indentLevel :: Int,  -- The indent level in spaces (add two for each
                         -- indent in occam, four in rain)
  outerItem :: [String], -- What we are currently inside for Structureds, e.g. "IF" or "SEQ".  Use the head of the list
  useOriginalName :: Bool, -- Whether to use the original names
  realCode :: Bool, -- Whether to leave out all helpful hints (e.g. {protocol} on Protocols)
  originalNames :: Map.Map String String,
  suppressNextIndent :: Bool,
  -- Used to pass down variables for input modes, or for subscripts:
  tempItem :: CodeWriter ()
}

type CodeWriter a = StateT ShowCodeState (Writer [String]) a

initialShowCodeState :: Map.Map String String -> ShowCodeState
initialShowCodeState origNames = ShowCodeState
  {indentLevel = 0, outerItem = [], useOriginalName = True, realCode = True, 
   originalNames = origNames,suppressNextIndent = False, tempItem = return ()}

showInputModeOccamM :: A.Variable -> A.InputMode -> CodeWriter ()
showInputModeOccamM v im = do modify (\s -> s {tempItem = showOccamM v})
                              showOccamM im

showSubscriptOccamM :: ShowOccam a => a -> A.Subscript -> CodeWriter ()
showSubscriptOccamM arr s = do modify (\s -> s {tempItem = showOccamM arr})
                               showOccamM s

suppressIndent :: CodeWriter ()
suppressIndent = do st <- get
                    put (st {suppressNextIndent = True})

showOccamLine :: CodeWriter () -> CodeWriter ()
showOccamLine s = do st <- get
                     if (suppressNextIndent st)
                       then do put (st {suppressNextIndent = False})
                       else tell [replicate (indentLevel st) ' ']
                     s
                     tell ["\n"]
                     
showRainLine :: CodeWriter () -> CodeWriter ()
showRainLine s = do st <- get
                    tell [replicate (indentLevel st) ' ']
                    s
                    tell ["\n"]

occamIndent :: CodeWriter ()
occamIndent = do st <- get
                 put (st { indentLevel = (indentLevel st) + 2} )

occamOutdent :: CodeWriter ()
occamOutdent = do st <- get
                  put (st { indentLevel = (indentLevel st) - 2} )

occamBlock :: CodeWriter () -> CodeWriter ()
occamBlock s = occamIndent >> s >> occamOutdent

rainIndent :: CodeWriter ()
rainIndent = do st <- get
                put (st { indentLevel = (indentLevel st) + 4} )

rainOutdent :: CodeWriter ()
rainOutdent = do st <- get
                 put (st { indentLevel = (indentLevel st) - 4} )

rainBlock :: CodeWriter () -> CodeWriter ()
rainBlock s = rainIndent >> s >> rainOutdent


showName :: A.Name -> CodeWriter ()
showName n = do st <- get
                tell [if useOriginalName st then Map.findWithDefault k k (originalNames st) else k]
  where k = A.nameName n

-- | Displays helper tags, as long as realCode isn't True
helper :: String -> CodeWriter ()
helper s = do st <- get
              tell $ singleton $ if (realCode st) then "" else s

currentContext :: CodeWriter String
currentContext = get >>= (return . head . outerItem)

pushContext :: String -> CodeWriter String
pushContext x = do st <- get
                   put (st {outerItem = (x:(outerItem st))})
                   return ""

beginStr :: String -> CodeWriter ()
beginStr n = pushContext n >> occamIndent

endStr :: CodeWriter ()
endStr = popContext >> occamOutdent

popContext :: CodeWriter ()
popContext = do st <- get
                put (st {outerItem = tail (outerItem st)})

doStr :: String -> CodeWriter () -> CodeWriter ()
doStr n s = showOccamLine (tell [n]) >> (beginStr n) >> s >> endStr

--TODO remove these functions?  Or at least rename them
showOccam :: ShowOccam a => a -> String
showOccam x = concat $ snd $ runWriter $ evalStateT (showOccamM x) (initialShowCodeState Map.empty)

showRain :: ShowRain a => a -> String
showRain x = concat $ snd $ runWriter $ evalStateT (showRainM x) (initialShowCodeState Map.empty)


bracket :: MonadWriter [String] m => m () -> m ()
bracket x = tell ["("] >> x >> tell [")"]
                
-- | A type-class that indicates that the data (AST item) is displayable as occam code.
class ShowOccam a where
  showOccamM :: a -> CodeWriter ()

-- | A type-class that indicates that the data (AST item) is displayable as Rain code.
class ShowRain a where
  showRainM :: a -> CodeWriter ()

-- | Shows the given code (AST item) as either occam or Rain code, depending on which frontend was selected
showCode :: (CSMR m, ShowOccam a, ShowRain a) => a -> m String
showCode o
   = do st <- getCompState
        case csFrontend st of
          FrontendOccam -> return $ concat $ snd $ runWriter $ evalStateT (showOccamM o)
            (initialShowCodeState $ transformNames $ csNames st)
          FrontendRain -> return $ concat $ snd $ runWriter $ evalStateT (showRainM o)
            (initialShowCodeState $ transformNames $ csNames st)
 where
   transformNames :: Map.Map String A.NameDef -> Map.Map String String
   transformNames = Map.map A.ndOrigName

-- | Some type hackery to allow formatCode to take a variable number of functions.
class CSMR m => ShowCodeFormat a m | a -> m where
  chain :: [String] -> [m String] -> a

instance CSMR m => ShowCodeFormat (m String) m where
  chain xs ys = (liftM concat) (sequence $ interleave (map return xs) (ys))
    where
      --Given [a,b,c] [1,2], produces [a,1,b,2,c] etc
      interleave :: [a] -> [a] -> [a]
      interleave xs [] = xs
      interleave [] ys = ys
      interleave (x:xs) (y:ys) = (x:y: (interleave xs ys))


instance (ShowOccam a, ShowRain a, ShowCodeFormat r m, CSMR m) => ShowCodeFormat (a -> r) m where
  chain a x = (\y -> chain a (x ++ [showCode y]))
              

-- | Formats the given code as either occam or Rain code, depending on the frontend (using showCode).
-- Use like this:
-- dieC $ formatCode "Types do not match: % and %" ta tb
formatCode :: (CSMR m,ShowCodeFormat r m) => String -> r
formatCode fmt = chain (splitRegex (mkRegex "%") fmt) []


--Type-class instances follow for ShowOccam and ShowRain:

instance ShowOccam A.Name where
  showOccamM n = showName n

instance ShowRain A.Name where
  showRainM n = showName n

instance ShowOccam A.Type where
  showOccamM A.Bool = tell ["BOOL"]
  showOccamM A.Byte = tell ["BYTE"]
  showOccamM A.UInt16 = tell ["UINT16"]
  showOccamM A.UInt32 = tell ["UINT32"]
  showOccamM A.UInt64 = tell ["UINT64"]
  showOccamM A.Int = tell ["INT"]
  showOccamM A.Int8 = tell ["INT8"]
  showOccamM A.Int16 = tell ["INT16"]
  showOccamM A.Int32 = tell ["INT32"]
  showOccamM A.Int64 = tell ["INT64"]
  showOccamM A.Real32 = tell ["REAL32"]
  showOccamM A.Real64 = tell ["REAL64"]
  showOccamM A.Any = tell ["ANY"]
  showOccamM (A.Timer _) = tell ["TIMER"]
  showOccamM A.Time = tell ["TIME"]
  showOccamM (A.UnknownVarType en)
    = do tell ["(inferred type for: "]
         either showName (const $ return ()) en
         tell [")"]
  showOccamM (A.UnknownNumLitType m _ n)
    = tell ["(inferred numeric type: ",show m," ",show n,")"]
  showOccamM (A.Mobile t) = tell ["MOBILE "] >> showOccamM t
  showOccamM (A.Array ds t)
      = (sequence dims) >> showOccamM t
    where
      dims = [case d of
                A.Dimension n -> tell ["["] >> showOccamM n >> tell ["]"]
                A.UnknownDimension -> tell ["[]"]
              | d <- ds]
  showOccamM (A.Chan _ _ t) = tell ["CHAN "] >> showOccamM t
  showOccamM (A.Counted ct et) = showOccamM ct >> tell ["::"] >> showOccamM et
  showOccamM (A.Port t) = tell ["PORT "] >> showOccamM t
  showOccamM (A.UserDataType n) = showName n >> helper "{data type}"
  showOccamM (A.Record n) = showName n >> helper "{record}"
  showOccamM (A.UserProtocol n) = showName n >> helper "{protocol}"
  showOccamM (A.List t) = tell ["LIST "] >> showOccamM t

instance ShowRain A.Type where
  showRainM A.Bool = tell ["bool"]
  showRainM A.Byte = tell ["uint8"]
  showRainM A.UInt16 = tell ["uint16"]
  showRainM A.UInt32 = tell ["uint32"]
  showRainM A.UInt64 = tell ["uint64"]
  showRainM A.Int8 = tell ["sint8"]
  showRainM A.Int16 = tell ["sint16"]
  showRainM A.Int32 = tell ["sint32"]
  showRainM A.Int64 = tell ["int"]
  showRainM A.Int = tell ["int"]
  showRainM (A.Chan dir attr t) 
    = case dir of
        A.DirUnknown -> tell ["channel ", ao (A.caWritingShared attr),
          "2", ao (A.caReadingShared attr)," "] >> showRainM t
        A.DirInput -> tell [if A.caReadingShared attr then "shared" else "", " ?"] >> showRainM t
        A.DirOutput -> tell [if A.caWritingShared attr then "shared" else "", " !"] >> showRainM t
    where
      ao :: Bool -> String
      ao b = if b then "any" else "one"  
  showRainM A.Time = tell ["time"]
  -- Mobility is not explicit in Rain:
  showRainM (A.Mobile t) = showRainM t
  showRainM (A.List t) = tell ["["] >> showRainM t >> tell ["]"]
  showRainM (A.UnknownVarType en)
    = do tell ["(inferred type for: "]
         either showName (const $ return ()) en
         tell [")"]
  showRainM (A.UnknownNumLitType m _ n)
    = tell ["(inferred numeric type: ",show m," ",show n,")"]
  showRainM x = tell ["<invalid Rain type: ", show x, ">"]

instance ShowOccam A.DyadicOp where
  showOccamM A.Add = tell ["+"]
  showOccamM A.Subtr = tell ["-"]
  showOccamM A.Mul = tell ["*"]
  showOccamM A.Div = tell ["/"]
  showOccamM A.Rem = tell ["REM"]
  showOccamM A.Plus = tell ["PLUS"]
  showOccamM A.Minus = tell ["MINUS"]
  showOccamM A.Times = tell ["TIMES"]
  showOccamM A.BitAnd = tell ["/\\"]
  showOccamM A.BitOr = tell ["\\/"]
  showOccamM A.BitXor = tell ["><"]
  showOccamM A.LeftShift = tell ["<<"]
  showOccamM A.RightShift = tell [">>"]
  showOccamM A.And = tell ["AND"]
  showOccamM A.Or = tell ["OR"]
  showOccamM A.Eq = tell ["="]
  showOccamM A.NotEq = tell ["<>"]
  showOccamM A.Less = tell ["<"]
  showOccamM A.More = tell [">"]
  showOccamM A.LessEq = tell ["<="]
  showOccamM A.MoreEq = tell [">="]
  showOccamM A.After = tell ["AFTER"]


instance ShowRain A.DyadicOp where
  showRainM A.Div = tell ["/"]
  showRainM A.Rem = tell ["%"]
  showRainM A.Plus = tell ["+"]
  showRainM A.Minus = tell ["-"]
  showRainM A.Times = tell ["*"]
  showRainM A.And = tell ["and"]
  showRainM A.Or = tell ["or"]
  showRainM A.Eq = tell ["=="]
  showRainM A.NotEq = tell ["<>"]
  showRainM A.Less = tell ["<"]
  showRainM A.More = tell [">"]
  showRainM A.LessEq = tell ["<="]
  showRainM A.MoreEq = tell [">="]
  showRainM x = tell ["<invalid Rain operator: ", show x, ">"]

instance ShowOccam A.MonadicOp where
  showOccamM A.MonadicSubtr = tell ["-"]
  showOccamM A.MonadicMinus = tell ["MINUS"]
  showOccamM A.MonadicBitNot = tell ["~"]
  showOccamM A.MonadicNot = tell ["NOT"]

instance ShowOccam A.Variable where
  showOccamM (A.Variable _ n) = showName n
  showOccamM (A.SubscriptedVariable _ s v) = showSubscriptOccamM v s
  showOccamM (A.DirectedVariable _ A.DirUnknown v) = showOccamM v
  showOccamM (A.DirectedVariable _ A.DirInput v) = showOccamM v >> tell ["?"]
  showOccamM (A.DirectedVariable _ A.DirOutput v) = showOccamM v >> tell ["!"]
  
instance ShowRain A.Variable where
  showRainM (A.Variable _ n) = showName n
  showRainM (A.DirectedVariable _ A.DirInput v) = tell ["?"] >> showRainM v
  showRainM (A.DirectedVariable _ A.DirOutput v) = tell ["!"] >> showRainM v
  showRainM x = tell ["<invalid Rain variable: ", show x, ">"]

instance ShowOccam A.ArrayElem where
  showOccamM (A.ArrayElemArray elems) = tell ["["] >> showWithCommas elems >> tell ["]"]
  showOccamM (A.ArrayElemExpr e) = showOccamM e

instance ShowOccam A.LiteralRepr where
  showOccamM (A.RealLiteral _ s) = tell [s]
  showOccamM (A.IntLiteral _ s) = tell [s]
  showOccamM (A.HexLiteral _ s) = tell ["#", s]
  showOccamM (A.ByteLiteral _ s) = tell ["'", s, "'"]
  showOccamM (A.ArrayLiteral _ elems) = tell ["["] >> showWithCommas elems >> tell ["]"]  
  --TODO record literals

instance ShowOccam A.Subscript where
  showOccamM (A.Subscript _ _ e) = getTempItem >> tell ["["] >> showOccamM e >> tell ["]"]
  showOccamM (A.SubscriptField _ n) = getTempItem >> tell ["["] >> showName n >> tell ["]"]
  showOccamM (A.SubscriptFromFor _ start count)
    = tell ["["] >> getTempItem >> tell [" FROM "] >> showOccamM start >> tell [" FOR "] >> showOccamM count >> tell ["]"]
  showOccamM (A.SubscriptFor _ count)
    = tell ["["] >> getTempItem >> tell [" FOR "] >> showOccamM count >> tell ["]"]
  showOccamM (A.SubscriptFrom _ start)
    = tell ["["] >> getTempItem >> tell [" FROM "] >> showOccamM start >> tell ["]"]        
  

convOrSpace :: A.ConversionMode -> CodeWriter ()
convOrSpace A.DefaultConversion = space
convOrSpace A.Round = tell [" ROUND "]
convOrSpace A.Trunc = tell [" TRUNC "]

instance ShowOccam A.Expression where
  showOccamM (A.Monadic _ op e) = bracket $ showOccamM op >> space >> showOccamM e
  showOccamM (A.Dyadic _ op lhs rhs) = bracket $ showOccamM lhs >> space >> showOccamM op >> space >> showOccamM rhs
  showOccamM (A.MostPos _ t) = bracket $ tell ["MOSTPOS "] >> showOccamM t
  showOccamM (A.MostNeg _ t) = bracket $ tell ["MOSTNEG "] >> showOccamM t
  showOccamM (A.SizeType _ t) = bracket $ tell ["SIZE "] >> showOccamM t
  showOccamM (A.SizeExpr _ e) = bracket $ tell ["SIZE "] >> showOccamM e
  showOccamM (A.SizeVariable _ v) = bracket $ tell ["SIZE "] >> showOccamM v
  showOccamM (A.Conversion _ cm t e) = bracket $ showOccamM t >> convOrSpace cm >> showOccamM e
  showOccamM (A.ExprVariable _ v) = showOccamM v
  showOccamM (A.Literal _ _ lit) = showOccamM lit
  showOccamM (A.True _) = tell ["TRUE"]
  showOccamM (A.False _) = tell ["FALSE"]
  showOccamM (A.FunctionCall _ n es) = showName n >> tell ["("] >> showWithCommas es >> tell [")"]
  showOccamM (A.SubscriptedExpr _ s e) = showSubscriptOccamM e s
  showOccamM (A.BytesInExpr _ e) = bracket $ tell ["BYTESIN "] >> showOccamM e
  showOccamM (A.BytesInType _ t) = bracket $ tell ["BYTESIN "] >> showOccamM t
  showOccamM (A.OffsetOf _ t n) = tell ["OFFSETOF("] >> showOccamM t >> tell [" , "] >> showName n >> tell [")"]
  --TODO exprconstr

instance ShowOccam A.Formal where
  showOccamM (A.Formal am t n) = (maybeVal am)
                                 >> (showOccamM t)
                                 >> space
                                 >> (showName n)
                  
space :: CodeWriter ()
space = tell [" "]

colon :: CodeWriter ()
colon = tell [":"]

maybeVal :: A.AbbrevMode -> CodeWriter ()
maybeVal am = tell [if (am == A.ValAbbrev) then "VAL " else ""]

instance ShowOccam A.Specification where
  -- TODO add specmode to the output
  showOccamM (A.Specification _ n (A.Proc _ sm params body))
    = do let params' = intersperse (tell [","]) $ map showOccamM params
         showOccamLine $ do tell ["PROC "]
                            showName n
                            tell ["("]
                            sequence_ params'
                            tell [")"]
         occamIndent
         showOccamM body
         occamOutdent
         showOccamLine (tell [":"])
  showOccamM (A.Specification _ n (A.Declaration _ t))
    = showOccamLine $ showOccamM t >> space >> showName n >> colon
  showOccamM (A.Specification _ n (A.Is _ am t v))
    = showOccamLine $ (maybeVal am) >> showOccamM t >> space >> showName n >> tell [" IS "] >> showOccamM v >> colon
  showOccamM (A.Specification _ n (A.IsExpr _ am t e))
    = showOccamLine $ (maybeVal am) >> showOccamM t >> space >> showName n >> tell [" IS "] >> showOccamM e >> colon
  showOccamM (A.Specification _ n (A.IsChannelArray _ t vs))
    = showOccamLine $ showOccamM t >> space >> showName n >> tell [" IS ["] >> showWithCommas vs >> tell ["]:"]
  showOccamM (A.Specification _ n (A.DataType _ t))
    = showOccamLine $ tell ["DATA TYPE "] >> showName n >> tell [" IS "] >> showOccamM t >> colon
  showOccamM (A.Specification _ n (A.RecordType _ packed fields))
    = do (showOccamLine $ tell ["DATA TYPE "] >> showName n)
         occamIndent
         (showOccamLine $ tell [if packed then "PACKED RECORD" else "RECORD"])
         occamIndent
         (sequence_ (map (\(n,t) -> showOccamLine $ showOccamM t >> space >> showName n >> colon) fields))
         occamOutdent
         occamOutdent
         (showOccamLine colon)
  --TODO use the specmode
  showOccamM (A.Specification _ n (A.Function _ sm retTypes params (Left el@(A.Only {}))))
    = showOccamLine $
        showWithCommas retTypes >> (tell [" FUNCTION "]) >> showName n >> tell ["("] >> showWithCommas params >> tell [")"]
        >> tell [" IS "] >> showOccamM el >> colon
  showOccamM (A.Specification _ n (A.Function _ sm retTypes params (Left body)))
    = (showOccamLine $ showWithCommas retTypes >> (tell [" FUNCTION "]) >> showName n >> tell ["("] >> showWithCommas params >> tell [")"])
      >> occamIndent
      >> showOccamM body
      >> occamOutdent
      >> showOccamLine colon
  showOccamM (A.Specification _ n (A.Protocol _ ts))
    = showOccamLine $ tell ["PROTOCOL "] >> showName n >> tell [" IS "] >> showWithSemis ts >> colon
  showOccamM (A.Specification _ n (A.ProtocolCase _ nts))
    = (showOccamLine $ tell ["PROTOCOL "] >> showName n) >> occamBlock
        (showOccamLine (tell ["CASE"]) >> occamBlock
          (sequence_ $ map (showOccamLine . showProtocolItem) nts)
      ) >> colon
  showOccamM (A.Specification _ n (A.Retypes _ am t v))
    = showOccamLine $ maybeVal am >> showOccamM t >> space >> showName n >> tell [" RETYPES "] >> showOccamM v >> colon
  showOccamM (A.Specification _ n (A.RetypesExpr _ am t e))
    = showOccamLine $ maybeVal am >> showOccamM t >> space >> showName n >> tell [" RETYPES "] >> showOccamM e >> colon
  
showProtocolItem :: (A.Name, [A.Type]) -> CodeWriter ()
showProtocolItem (n,ts) = sequence_ $ intersperse (tell [" ; "]) $
  showName n : (map showOccamM ts)
  
instance ShowOccam A.Variant where
  showOccamM (A.Variant _ n iis p)
    = (showOccamLine (sequence_ $ intersperse (tell [" ; "]) $ [showName n] ++ (map showOccamM iis)))
      >> occamIndent >> showOccamM p >> occamOutdent
           
instance ShowOccam A.Actual where
  showOccamM (A.ActualVariable v) = showOccamM v
  showOccamM (A.ActualExpression e) = showOccamM e
  
instance ShowOccam A.OutputItem where
  showOccamM (A.OutExpression _ e) = showOccamM e
  showOccamM (A.OutCounted _ ce ae) = showOccamM ce >> tell [" :: "] >> showOccamM ae
  
getTempItem :: CodeWriter ()
getTempItem = get >>= tempItem

instance ShowOccam A.InputItem where 
  showOccamM (A.InVariable _ v) = showOccamM v
  showOccamM (A.InCounted _ cv av) = showOccamM cv >> tell [" :: "] >> showOccamM av
  
instance ShowOccam A.InputMode where
  showOccamM (A.InputSimple _ iis)
    = showOccamLine $ getTempItem >> tell [" ? "] >> (showWithSemis iis)
  showOccamM (A.InputCase _ str)
    = (showOccamLine $ getTempItem >> tell [" ? CASE"]) >> occamIndent >> showOccamM str >> occamOutdent
  showOccamM (A.InputTimerRead _ ii)
    = showOccamLine $ getTempItem >> tell [" ? "] >> showOccamM ii
  showOccamM (A.InputTimerAfter _ e)
    = showOccamLine $ getTempItem >> tell [" ? AFTER "] >> showOccamM e
  
  
instance ShowOccam A.Alternative where
  showOccamM (A.Alternative _ e v im p)
    = do showOccamM e
         tell [" & "]
         suppressIndent
         showInputModeOccamM v im
         occamIndent
         showOccamM p
         occamOutdent
  
instance ShowOccam A.Replicator where
  showOccamM (A.For _ n start count) = tell [" "] >> showName n >> tell [" = "] >> showOccamM start >> tell [" FOR "] >> showOccamM count
  showOccamM (A.ForEach _ n e) = tell [" "] >> showName n >> tell [" IN "] >> showOccamM e

instance ShowOccam A.Choice where
  showOccamM (A.Choice _ e p) = showOccamLine (showOccamM e) >> occamBlock (showOccamM p)

instance ShowOccam A.Option where
  showOccamM (A.Option _ es p) = showOccamLine (sequence_ $ intersperse (tell [" , "]) $ map showOccamM es) >> occamBlock (showOccamM p)
  showOccamM (A.Else _ p) = showOccamLine (tell ["ELSE"]) >> occamBlock (showOccamM p)

instance (Data a, ShowOccam a) => ShowOccam (A.Structured a) where
  showOccamM (A.Spec _ spec str) = showOccamM spec >> showOccamM str
  showOccamM (A.Rep _ rep str)
    = do item <- currentContext
         (showOccamLine (return (item ++ " ") >> showOccamM rep)) >> occamIndent >> showOccamM str >> occamOutdent
  showOccamM (A.Only _ p) = showOccamM p
  showOccamM (A.Several _ ss) = sequence_ $ map showOccamM ss
  showOccamM (A.ProcThen _ p str) = showOccamLine (tell ["VALOF"]) >> occamBlock (showOccamM p >> showOccamLine (tell ["RESULT "] >> showOccamM str))

showWithCommas :: ShowOccam a => [a] -> CodeWriter ()
showWithCommas ss = sequence_ $ intersperse (tell [" , "]) $ map showOccamM ss

showWithSemis :: ShowOccam a => [a] -> CodeWriter ()
showWithSemis ss = sequence_ $ intersperse (tell [" ; "]) $ map showOccamM ss

instance ShowOccam A.ExpressionList where
  showOccamM (A.ExpressionList _ es) = showWithCommas es
  --TODO functioncalllist

outer :: (Data a, ShowOccam a) => String -> A.Structured a -> CodeWriter ()
outer keyword (A.Rep _ rep str)
  = do showOccamLine (tell [keyword] >> showOccamM rep)
       beginStr keyword
       showOccamM str
       endStr
outer keyword str = doStr keyword (showOccamM str)

instance ShowOccam A.Process where
  showOccamM (A.Assign _ vs el) = showOccamLine (showWithCommas vs >> tell [":="] >> showOccamM el)
  showOccamM (A.Skip _) = showOccamLine $ tell ["SKIP"]
  showOccamM (A.Stop _) = showOccamLine $ tell ["STOP"] 
  showOccamM (A.Input _ v im) = showInputModeOccamM v im
  showOccamM (A.Output _ v ois) = showOccamLine $ showOccamM v >> tell [" ! "] >> (showWithSemis ois)
  showOccamM (A.OutputCase _ v n ois) = showOccamLine $ showOccamM v >> tell [" ! "] >> 
    (sequence_ $ intersperse (tell [" ; "]) $ [showName n] ++ (map showOccamM ois))
  --TODO gettime and wait ?
  
  --TODO proccall
  showOccamM (A.ProcCall _ n params) = showOccamLine $ showName n >> tell [" ( "] >> showWithCommas params >> tell [" ) "]
  showOccamM (A.While _ e p) = (showOccamLine $ tell ["WHILE "] >> showOccamM e) >> occamIndent >> showOccamM p >> occamOutdent
  showOccamM (A.Case _ e s) = (showOccamLine $ tell ["CASE "] >> showOccamM e) >> occamBlock (showOccamM s)
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
  showRainM = const $ return ()

instance ShowOccam a => ShowOccam [a] where
  showOccamM xs = tell ["["] >> sequence (intersperse (tell [", "]) $ map
    showOccamM xs) >> tell ["]"]
instance ShowRain a => ShowRain [a] where
  showRainM xs = tell ["["] >> sequence (intersperse (tell [", "]) $ map
    showRainM xs) >> tell ["]"]


-- | Extends an existing (probably generic) function with cases for everything that has a specific ShowOccam and ShowRain instance
-- This is a bit of manual wiring.  Because we can't generically deduce whether or not 
-- a given Data item has a showRain\/showOccam implementation (that I know of), I have 
-- had to add this function that has a line for each type that does have a 
-- ShowOccam\/ShowRain implementation.  But since to add a type to the ShowOccam\/ShowRain 
-- classes you have to provide a specific instance above anyway, I don't think that adding 
-- one more line while you're at it is too bad.
extCode :: (Data b, Typeable b) => (b -> Doc) -> (forall a. (ShowOccam a, ShowRain a) => a -> String) -> (b -> Doc)
extCode q f = q 
                `extQ` (text . (f :: A.DyadicOp -> String))
                `extQ` (text . (f :: A.Expression -> String))
                `extQ` (text . (f :: A.ExpressionList -> String))
                `extQ` (text . (f :: A.Formal -> String))
                `extQ` (text . (f :: A.MonadicOp -> String))
                `extQ` (text . (f :: A.Process -> String))
                `extQ` (text . (f :: A.Replicator -> String))
                `extQ` (text . (f :: A.Specification -> String))
                `extQ` (text . (f :: A.Type -> String))
                `extQ` (text . (f :: A.Variable -> String))
--TODO
--                `ext1Q` (text . (f :: (Data c, ShowOccam c) => A.Structured c -> String))

