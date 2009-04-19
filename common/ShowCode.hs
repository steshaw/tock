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


-- TOO: This module is still a bit of a mess.  I've put in some settings but
-- some of them (such as realCode) are not wired up, and there's no easy way
-- to set them from outside this module.  Also, some things aren't quite right
-- (such as replicated IFs), and due to the way the occam parser works, a few
-- SEQs get introduced if you parse a file then write it out again straight
-- away.

-- So I'm committing this for the time being, but it really does need some work (and some tests, of course*) later on.

-- My plan for testing was to take each of the cgtests, and parse it in to AST_A.  Then print AST_A using this
-- module, and feed it back in to the parser to get AST_B.  Then check if AST_A and AST_B are equal.

module ShowCode (showCode, ShowOccam(..), showOccam, ShowRain(..), showRain, formatCode) where 

import Control.Monad.State
import Control.Monad.Writer
import Data.Generics (Data, gshow)
import Data.List
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ hiding (space, colon, semi)
import Text.Regex

import qualified AST as A
import CompState hiding (CSM) -- everything here is read-only
import Operators
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

showRainLine' :: CodeWriter () -> CodeWriter ()
showRainLine' s = showRainLine $ s >> tell [";"]

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
rainBlock s = currentContext >>= \c -> showRainLine (tell [c]) >> showRainLine (tell ["{"]) >> rainIndent >> s >> rainOutdent >>
  showRainLine (tell ["}"])


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

-- For printing out the A.AST type, we need an instance for the unit type:
instance ShowOccam () where
  showOccamM _ = return ()
instance ShowRain () where
  showRainM _ = return ()

-- | Shows the given code (AST item) as either occam or Rain code, depending on which frontend was selected
showCode :: (CSMR m, ShowOccam a, ShowRain a) => a -> m String
showCode o
   = do st <- getCompState
        case csFrontend $ csOpts st of
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

instance ShowOccam A.Dimension where
  showOccamM (A.Dimension n) = tell ["["] >> showOccamM n >> tell ["]"]
  showOccamM A.UnknownDimension = tell ["[]"]

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
  showOccamM A.Infer = tell ["inferred type"]
  showOccamM A.Barrier = tell ["BARRIER"]
  showOccamM (A.UnknownVarType _ en)
    = do tell ["(inferred type for: "]
         either showName (tell . (:[]) . show) en
         tell [")"]
  showOccamM (A.UnknownNumLitType m _ n)
    = tell ["(inferred numeric type: ",show m," ",show n,")"]
  showOccamM (A.Mobile t) = tell ["MOBILE "] >> showOccamM t
  showOccamM (A.Array ds t)
      = mapM showOccamM ds >> showOccamM t
  showOccamM (A.ChanEnd dir ca t)
      = tell [shared, "CHAN", direction, " "] >> showOccamM t
    where
      shared
          = case ca of
              A.Unshared -> ""
              A.Shared -> "SHARED "
      direction
          = case dir of
              A.DirInput -> "?"
              A.DirOutput -> "!"
  showOccamM (A.Chan ca t)
      = tell [shared, "CHAN "] >> showOccamM t
    where
      shared
          = case (A.caWritingShared ca, A.caReadingShared ca) of
              (A.Unshared, A.Unshared) -> ""
              (A.Shared, A.Unshared) -> "SHARED! "
              (A.Unshared, A.Shared) -> "SHARED? "
              (A.Shared, A.Shared) -> "SHARED "
  showOccamM (A.ChanDataType dir sh n)
    = do when (sh == A.Shared) $ tell ["SHARED "]
         showName n
         tell [if dir == A.DirInput then "?" else "!"]
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
  showRainM (A.Chan attr t) 
    = tell ["channel ", ao (A.caWritingShared attr),
          "2", ao (A.caReadingShared attr)," "] >> showRainM t
    where
      ao :: A.ShareMode -> String
      ao b = if b == A.Shared then "any" else "one"  
  showRainM (A.ChanEnd dir attr t) 
    = case dir of
        A.DirInput -> tell [if attr == A.Shared then "shared" else "", " ?"] >> showRainM t
        A.DirOutput -> tell [if attr == A.Shared then "shared" else "", " !"] >> showRainM t
    where
      ao :: Bool -> String
      ao b = if b then "any" else "one"  
  showRainM A.Time = tell ["time"]
  -- Mobility is not explicit in Rain, but we should indicate it:
  showRainM (A.Mobile t) = tell ["<mobile>"] >> showRainM t
  showRainM (A.List t) = tell ["["] >> showRainM t >> tell ["]"]
  showRainM (A.UnknownVarType _ en)
    = do tell ["(inferred type for: "]
         either showName (tell . (:[]) . show) en
         tell [")"]
  showRainM (A.UnknownNumLitType m _ n)
    = tell ["(inferred numeric type: ",show m," ",show n,")"]
  showRainM x = tell ["<invalid Rain type: ", show x, ">"]

instance ShowOccam A.Variable where
  showOccamM (A.Variable _ n) = showName n
  showOccamM (A.SubscriptedVariable _ s v) = showSubscriptOccamM v s
  showOccamM (A.DirectedVariable _ A.DirInput v) = showOccamM v >> tell ["?"]
  showOccamM (A.DirectedVariable _ A.DirOutput v) = showOccamM v >> tell ["!"]
  showOccamM (A.DerefVariable _ v) = tell ["(DEREF "] >> showOccamM v >> tell [")"]
  showOccamM (A.VariableSizes _ v) = tell ["(SIZES "] >> showOccamM v >> tell [")"]
  
instance ShowRain A.Variable where
  showRainM (A.Variable _ n) = showName n
  showRainM (A.DirectedVariable _ A.DirInput v) = tell ["?"] >> showRainM v
  showRainM (A.DirectedVariable _ A.DirOutput v) = tell ["!"] >> showRainM v
  showRainM x = tell ["<invalid Rain variable: ", show x, ">"]

instance ShowOccam A.LiteralRepr where
  showOccamM (A.RealLiteral _ s) = tell [s]
  showOccamM (A.IntLiteral _ s) = tell [s]
  showOccamM (A.HexLiteral _ s) = tell ["#", s]
  showOccamM (A.ByteLiteral _ s) = tell ["'", s, "'"]
  showOccamM (A.ArrayListLiteral _ elems) = tell ["["] >> showOccamM elems >> tell ["]"]  
  showOccamM (A.RecordLiteral _ es) = tell ["["] >> showOccamM es >> tell ["]"]
  --TODO record literals

instance ShowRain A.LiteralRepr where
  showRainM (A.RealLiteral _ s) = tell [s]
  showRainM (A.IntLiteral _ s) = tell [s]
  showRainM (A.HexLiteral _ s) = tell ["#", s]
  showRainM (A.ByteLiteral _ s) = tell ["'", s, "'"]
  showRainM (A.ArrayListLiteral _ elems) = tell ["["] >> showRainM elems >> tell ["]"]  

instance ShowOccam A.Subscript where
  showOccamM (A.Subscript _ _ e) = getTempItem >> tell ["["] >> showOccamM e >> tell ["]"]
  showOccamM (A.SubscriptField _ n) = getTempItem >> tell ["["] >> showName n >> tell ["]"]
  showOccamM (A.SubscriptFromFor _ _ start count)
    = tell ["["] >> getTempItem >> tell [" FROM "] >> showOccamM start >> tell [" FOR "] >> showOccamM count >> tell ["]"]
  showOccamM (A.SubscriptFor _ _ count)
    = tell ["["] >> getTempItem >> tell [" FOR "] >> showOccamM count >> tell ["]"]
  showOccamM (A.SubscriptFrom _ _ start)
    = tell ["["] >> getTempItem >> tell [" FROM "] >> showOccamM start >> tell ["]"]        
  

convOrSpace :: A.ConversionMode -> CodeWriter ()
convOrSpace A.DefaultConversion = space
convOrSpace A.Round = tell [" ROUND "]
convOrSpace A.Trunc = tell [" TRUNC "]

showOccamFunctionCall :: A.Name -> [A.Expression] -> CodeWriter ()
showOccamFunctionCall n es
  = do mOp <- functionOperator' n
       case (mOp, es) of
         (Nothing, _) -> showName n >> tell ["("] >> showWithCommas es >> tell [")"]
         (Just op, [e]) -> tell [op, " "] >> showOccamM e
         (Just op, [e,f]) -> showOccamM e >> tell [" ", op, " "] >> showOccamM f
  where
    functionOperator' (A.Name _ n)
      = do origs <- get >>* originalNames
           case Map.lookup n origs of
             Nothing -> return Nothing
             Just orig
               | isOperator orig -> return $ Just orig
               | otherwise -> return Nothing

instance ShowOccam A.Expression where
  showOccamM (A.MostPos _ t) = bracket $ tell ["MOSTPOS "] >> showOccamM t
  showOccamM (A.MostNeg _ t) = bracket $ tell ["MOSTNEG "] >> showOccamM t
  showOccamM (A.SizeType _ t) = bracket $ tell ["SIZE "] >> showOccamM t
  showOccamM (A.SizeExpr _ e) = bracket $ tell ["SIZE "] >> showOccamM e
  showOccamM (A.Conversion _ cm t e) = bracket $ showOccamM t >> convOrSpace cm >> showOccamM e
  showOccamM (A.ExprVariable _ v) = showOccamM v
  showOccamM (A.Literal _ _ lit) = showOccamM lit
  showOccamM (A.True _) = tell ["TRUE"]
  showOccamM (A.False _) = tell ["FALSE"]
  showOccamM (A.FunctionCall _ n es) = showOccamFunctionCall n es
  showOccamM (A.IntrinsicFunctionCall _ n es) = tell [n, "("] >> showWithCommas es >> tell [")"]
  showOccamM (A.SubscriptedExpr _ s e) = showSubscriptOccamM e s
  showOccamM (A.BytesInExpr _ e) = bracket $ tell ["BYTESIN "] >> showOccamM e
  showOccamM (A.BytesInType _ t) = bracket $ tell ["BYTESIN "] >> showOccamM t
  showOccamM (A.OffsetOf _ t n) = tell ["OFFSETOF("] >> showOccamM t >> tell [" , "] >> showName n >> tell [")"]
  showOccamM (A.AllocMobile _ t me) = showOccamM t >> maybe (return ()) showOccamM me
  showOccamM (A.CloneMobile _ e) = tell["CLONE "] >> showOccamM e

instance ShowRain A.Expression where
  showRainM (A.MostPos _ t) = bracket $ tell ["MOSTPOS "] >> showRainM t
  showRainM (A.MostNeg _ t) = bracket $ tell ["MOSTNEG "] >> showRainM t
  showRainM (A.SizeType _ t) = bracket $ tell ["SIZE "] >> showRainM t
  showRainM (A.SizeExpr _ e) = bracket $ tell ["SIZE "] >> showRainM e
  showRainM (A.Conversion _ cm t e) = bracket $ showRainM t >> convOrSpace cm >> showRainM e
  showRainM (A.ExprVariable _ v) = showRainM v
  showRainM (A.Literal _ _ lit) = showRainM lit
  showRainM (A.True _) = tell ["TRUE"]
  showRainM (A.False _) = tell ["FALSE"]
  showRainM (A.FunctionCall _ n es) = showName n >> tell ["("] >> showWithCommas es >> tell [")"]
  showRainM (A.BytesInExpr _ e) = bracket $ tell ["BYTESIN "] >> showRainM e
  showRainM (A.BytesInType _ t) = bracket $ tell ["BYTESIN "] >> showRainM t
  showRainM (A.OffsetOf _ t n) = tell ["OFFSETOF("] >> showRainM t >> tell [" , "] >> showName n >> tell [")"]

{-  showRainM (A.ExprConstr _ (A.RepConstr _ _ n r e))
    = tell ["["] >> showRainM e >> tell ["|"] >> showName n >>
      showRainM r >> tell ["]"]
-}
instance ShowOccam A.Formal where
  showOccamM (A.Formal am (A.ChanEnd dir sh t) n)
    = do maybeVal am
         showOccamM sh
         tell ["CHAN "]
         showOccamM t
         space
         showName n
         showOccamM dir 
  showOccamM (A.Formal am (A.Array ds (A.ChanEnd dir sh t)) n)
    = do maybeVal am
         mapM_ showOccamM ds
         showOccamM sh
         tell ["CHAN "]
         showOccamM t
         space
         showName n
         showOccamM dir 
  showOccamM (A.Formal am t n) = (maybeVal am)
                                 >> (showOccamM t)
                                 >> space
                                 >> (showName n)

instance ShowOccam A.Direction where
  showOccamM A.DirInput = tell ["?"]
  showOccamM A.DirOutput = tell ["!"]

instance ShowOccam A.ShareMode where
  showOccamM A.Unshared = return ()
  showOccamM A.Shared = tell ["SHARED "]
  
space :: CodeWriter ()
space = tell [" "]

colon :: CodeWriter ()
colon = tell [":"]

semi :: CodeWriter ()
semi = tell [";"]

maybeVal :: A.AbbrevMode -> CodeWriter ()
maybeVal am = tell [if (am == A.ValAbbrev) then "VAL " else ""]

maybeValRain :: A.AbbrevMode -> CodeWriter ()
maybeValRain am = tell [if (am == A.ValAbbrev) then "const " else ""]

instance ShowOccam A.RecordAttr where
  showOccamM attr
    = do when (A.packedRecord attr) $ tell ["PACKED "]
         when (A.mobileRecord attr) $ tell ["MOBILE "]

instance ShowOccam A.RecMode where
  showOccamM A.Recursive = tell ["RECURSIVE "]
  showOccamM A.PlainRec = return ()

instance ShowOccam A.Specification where
  -- TODO add specmode to the output
  showOccamM (A.Specification _ n (A.Proc _ sm params (Just body)))
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
  showOccamM (A.Specification _ n (A.DataType _ t))
    = showOccamLine $ tell ["DATA TYPE "] >> showName n >> tell [" IS "] >> showOccamM t >> colon
  showOccamM (A.Specification _ n (A.ChanBundleType _ rm nts))
    = do showOccamLine $ showOccamM rm >> tell ["CHAN TYPE "] >> showName n
         occamIndent
         showOccamLine $ tell ["MOBILE RECORD"]
         occamIndent
         mapM_ showItem nts
         occamOutdent
         occamOutdent
         showOccamLine colon
    where
      -- Must put the direction after the variable:
      showItem (n, A.ChanEnd dir A.Unshared t)
        = showOccamLine $ do tell ["CHAN "]
                             showOccamM t
                             tell [" "]
                             showName n
                             showOccamM dir
                             colon

  showOccamM (A.Specification _ n (A.Forking _))
    = showOccamLine $ tell ["FORKING --"] >> showName n
  showOccamM (A.Specification _ n (A.RecordType _ attr fields))
    = do (showOccamLine $ tell ["DATA TYPE "] >> showName n)
         occamIndent
         (showOccamLine $ showOccamM attr >> tell ["RECORD"])
         occamIndent
         (sequence_ (map (\(n,t) -> showOccamLine $ showOccamM t >> space >> showName n >> colon) fields))
         occamOutdent
         occamOutdent
         (showOccamLine colon)
  --TODO use the specmode
  showOccamM (A.Specification _ n (A.Function _ sm retTypes params (Just (Left el@(A.Only {})))))
    = showOccamLine $
        showWithCommas retTypes >> (tell [" FUNCTION "]) >> showName n >> tell ["("] >> showWithCommas params >> tell [")"]
        >> tell [" IS "] >> showOccamM el >> colon
  showOccamM (A.Specification _ n (A.Function _ sm retTypes params (Just (Left body))))
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
  showOccamM (A.Specification _ n (A.Rep _ rep))
    = do item <- currentContext
         (showOccamLine (return (item ++ " ") >> showName n >> showOccamM rep))
           -- TODO handle the indent

  
showProtocolItem :: (A.Name, [A.Type]) -> CodeWriter ()
showProtocolItem (n,ts) = sequence_ $ intersperse (tell [" ; "]) $
  showName n : (map showOccamM ts)
  
instance ShowOccam A.Variant where
  showOccamM (A.Variant _ n iis p mp)
    = (showOccamLine (sequence_ $ intersperse (tell [" ; "]) $ [showName n] ++ (map showOccamM iis)))
      >> occamIndent >> showOccamM p >> doMaybe (fmap showOccamM mp) >> occamOutdent
           
instance ShowOccam A.Actual where
  showOccamM (A.ActualVariable v) = showOccamM v
  showOccamM (A.ActualExpression e) = showOccamM e
  showOccamM (A.ActualChannelArray vs) = tell ["["] >> showOccamM vs >> tell ["]"]
  showOccamM (A.ActualClaim v) = tell ["CLAIM "] >> showOccamM v
  
instance ShowOccam A.OutputItem where
  showOccamM (A.OutExpression _ e) = showOccamM e
  showOccamM (A.OutCounted _ ce ae) = showOccamM ce >> tell [" :: "] >> showOccamM ae
  
getTempItem :: CodeWriter ()
getTempItem = get >>= tempItem

instance ShowOccam A.InputItem where 
  showOccamM (A.InVariable _ v) = showOccamM v
  showOccamM (A.InCounted _ cv av) = showOccamM cv >> tell [" :: "] >> showOccamM av
  
instance ShowOccam A.InputMode where
  showOccamM (A.InputSimple _ iis Nothing)
    = showOccamLine $ getTempItem >> tell [" ? "] >> (showWithSemis iis)
  showOccamM (A.InputSimple _ iis (Just p))
    = do showOccamLine $ getTempItem >> tell [" ?? "] >> (showWithSemis iis)
         occamIndent
         showOccamM p
         occamOutdent
  showOccamM (A.InputCase _ ty str)
    = (showOccamLine $ getTempItem >> tell [op, "CASE"]) >> occamIndent >> showOccamM str >> occamOutdent
    where
      op = case ty of
             A.InputCaseNormal -> " ? "
             A.InputCaseExtended -> " ?? "
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
  showOccamM (A.For _ start count step) = tell [" = "] >> showOccamM start >> tell [" FOR "] >> showOccamM count
    >> tell [" STEP "] >> showOccamM step
  showOccamM (A.ForEach _ e) = tell [" IN "] >> showOccamM e

instance ShowOccam A.Choice where
  showOccamM (A.Choice _ e p) = showOccamLine (showOccamM e) >> occamBlock (showOccamM p)

instance ShowOccam A.Option where
  showOccamM (A.Option _ es p) = showOccamLine (sequence_ $ intersperse (tell [" , "]) $ map showOccamM es) >> occamBlock (showOccamM p)
  showOccamM (A.Else _ p) = showOccamLine (tell ["ELSE"]) >> occamBlock (showOccamM p)

instance (Data a, ShowOccam a) => ShowOccam (A.Structured a) where
  showOccamM (A.Spec _ spec str) = showOccamM spec >> showOccamM str
  showOccamM (A.Only _ p) = showOccamM p
  showOccamM (A.Several _ ss) = sequence_ $ map showOccamM ss
  showOccamM (A.ProcThen _ p str) = showOccamLine (tell ["VALOF"]) >> occamBlock (showOccamM p >> showOccamLine (tell ["RESULT "] >> showOccamM str))

showWithCommas :: ShowOccam a => [a] -> CodeWriter ()
showWithCommas ss = sequence_ $ intersperse (tell [" , "]) $ map showOccamM ss

showWithSemis :: ShowOccam a => [a] -> CodeWriter ()
showWithSemis ss = sequence_ $ intersperse (tell [" ; "]) $ map showOccamM ss

instance ShowOccam A.ExpressionList where
  showOccamM (A.ExpressionList _ es) = showWithCommas es
  showOccamM (A.FunctionCallList _ n es)
    = showOccamFunctionCall n es
  showOccamM (A.IntrinsicFunctionCallList _ n es)
    = tell [n, "("] >> showOccamM es >> tell [")"]
  showOccamM (A.AllocChannelBundle _ n)
    = tell ["MOBILE "] >> showOccamM n

instance ShowRain A.ExpressionList where
  showRainM (A.ExpressionList _ [e]) = showRainM e

outerOccam :: (Data a, ShowOccam a) => String -> A.Structured a -> CodeWriter ()
{- TODO get replicators working properly
outerOccam keyword (A.Rep _ n rep str)
  = do showOccamLine (tell [keyword] >> showOccamM rep)
       beginStr keyword
       showOccamM str
       endStr
-}
outerOccam keyword str = doStr keyword (showOccamM str)

outerRain :: (Data a, ShowRain a) => String -> A.Structured a -> CodeWriter ()
{- TODO get replicators working properly
outerRain keyword (A.Rep _ rep str)
  = do showRainLine (tell [keyword] >> showRainM rep)
       pushContext keyword
       rainBlock $ showRainM str
       popContext
-}
outerRain keyword str = pushContext keyword >> (rainBlock $ showRainM str)
  >> popContext

instance ShowOccam A.Process where
  showOccamM (A.Assign _ vs el) = showOccamLine (showWithCommas vs >> tell [":="] >> showOccamM el)
  showOccamM (A.Skip _) = showOccamLine $ tell ["SKIP"]
  showOccamM (A.Stop _) = showOccamLine $ tell ["STOP"] 
  showOccamM (A.Input _ v im) = showInputModeOccamM v im
  showOccamM (A.Output _ v ois) = showOccamLine $ showOccamM v >> tell [" ! "] >> (showWithSemis ois)
  showOccamM (A.OutputCase _ v n ois) = showOccamLine $ showOccamM v >> tell [" ! "] >> 
    (sequence_ $ intersperse (tell [" ; "]) $ [showName n] ++ (map showOccamM ois))
  --TODO gettime and wait ?
  
  showOccamM (A.ProcCall _ n params) = showOccamLine $ showName n >> tell [" ( "] >> showWithCommas params >> tell [" ) "]
  showOccamM (A.Fork _ Nothing p) = showOccamLine $ tell ["FORK "] >> showOccamM p
  showOccamM (A.Fork _ (Just n) p) = showOccamLine $ tell ["FORK "] >> showOccamM p
    >> tell [" --"] >> showName n
  showOccamM (A.IntrinsicProcCall _ n params) = showOccamLine $ tell [n, " ( "] >> showWithCommas params >> tell [" ) "]
  showOccamM (A.While _ e p) = (showOccamLine $ tell ["WHILE "] >> showOccamM e) >> occamIndent >> showOccamM p >> occamOutdent
  showOccamM (A.Case _ e s) = (showOccamLine $ tell ["CASE "] >> showOccamM e) >> occamBlock (showOccamM s)
  showOccamM (A.If _ str) = outerOccam "IF" str
  showOccamM (A.Alt _ False str) = outerOccam "ALT" str
  showOccamM (A.Alt _ True str) = outerOccam "PRI ALT" str
  showOccamM (A.Seq _ str) = outerOccam "SEQ" str
  showOccamM (A.Par _ A.PlainPar str) = outerOccam "PAR" str
  showOccamM (A.Par _ A.PriPar str) = outerOccam "PRI PAR" str
  showOccamM (A.Par _ A.PlacedPar str) = outerOccam "PLACED PAR" str
--  showOccamM _x = return $ "#error unimplemented" ++ show _x

-- TODO make this properly rain:
instance (Data a, ShowRain a) => ShowRain (A.Structured a) where
  showRainM (A.Spec _ spec str) = showRainM spec >> showRainM str
  showRainM (A.Only _ p) = showRainM p
  showRainM (A.Several _ ss) = sequence_ $ map showRainM ss
  showRainM (A.ProcThen _ p str) = showRainLine (tell ["VALOF"]) >> rainBlock (showRainM p >> showRainLine (tell ["RESULT "] >> showRainM str))

instance ShowRain A.Specification where
  -- TODO add specmode to the output
  showRainM (A.Specification _ n (A.Proc _ sm params body))
    = do let params' = intersperse (tell [","]) $ map showRainM params
         showRainLine $ do  tell ["process "]
                            showName n
                            tell ["("]
                            sequence_ params'
                            tell [")"]
         showRainLine (tell ["{"])
         rainIndent
         showRainM body
         rainOutdent
         showRainLine (tell ["}"])
  showRainM (A.Specification _ n (A.Declaration _ t))
    = showRainLine $ showRainM t >> colon >> showName n >> semi
  showRainM (A.Specification _ n (A.Is _ am t v))
    = showRainLine $ (maybeValRain am) >> showRainM t >> colon >> showName n >> tell [" = "] >> showRainM v >> semi


instance ShowRain A.Process where
  showRainM (A.Assign _ vs el) = showRainLine' (showWithCommas vs >> tell ["="] >> showRainM el)
  showRainM (A.Skip _) = showRainLine $ tell ["{}"]
  showRainM (A.Stop _) = showRainLine' $ tell ["STOP"] 
  showRainM (A.Input _ v im) = showInputModeOccamM v im --TODO add a rain version
  showRainM (A.Output _ v ois) = showRainLine' $ showRainM v >> tell [" ! "] >> (showWithSemis ois)
  showRainM (A.OutputCase _ v n ois) = showRainLine' $ showRainM v >> tell [" ! "] >> 
    (sequence_ $ intersperse (tell [" ; "]) $ [showName n] ++ (map showRainM ois))
  --TODO gettime and wait ?
  
  --TODO proccall
  showRainM (A.ProcCall _ n params) = showRainLine' $ showName n >> tell [" ( "] >> showWithCommas params >> tell [" ) "]
  showRainM (A.While _ e p) = (showRainLine $ tell ["while "] >> showRainM e) >> rainIndent >> showRainM p >> rainOutdent
  showRainM (A.Case _ e s) = (showRainLine $ tell ["case "] >> showRainM e) >> rainBlock (showRainM s)
  showRainM (A.If _ str) = outerRain "if" str
  showRainM (A.Alt _ False str) = outerRain "alt" str
  showRainM (A.Alt _ True str) = outerRain "pri alt" str
  showRainM (A.Seq _ str) = outerRain "seq" str
  showRainM (A.Par _ A.PlainPar str) = outerRain "par" str
  showRainM (A.Par _ A.PriPar str) = outerRain "pri par" str
  showRainM (A.Par _ A.PlacedPar str) = outerRain "placed par" str

instance ShowRain A.Replicator where
  showRainM (A.For _ start count _) = tell [" = "] >> showRainM start >> tell [" for "] >> showRainM count
  showRainM (A.ForEach _ e) = tell ["each ("] >> colon >> showRainM e

--TEMP:
instance Data a => ShowRain a where
  showRainM = tell . singleton . gshow

instance ShowOccam String where
  showOccamM s = tell [s]

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
{-
extCode :: (Data b, Typeable b) => (b -> Doc) -> (forall a. (ShowOccam a, ShowRain a) => a -> String) -> (b -> Doc)
extCode q f = q 
                `extQ` (text . (f :: A.Expression -> String))
                `extQ` (text . (f :: A.ExpressionList -> String))
                `extQ` (text . (f :: A.Formal -> String))
                `extQ` (text . (f :: A.Process -> String))
                `extQ` (text . (f :: A.Replicator -> String))
                `extQ` (text . (f :: A.Specification -> String))
                `extQ` (text . (f :: A.Type -> String))
                `extQ` (text . (f :: A.Variable -> String))
--TODO
--                `ext1Q` (text . (f :: (Data c, ShowOccam c) => A.Structured c -> String))
-}
