-- | Generate C code from the mangled AST.
module GenerateCPPCSP where

import Data.Char
import Data.List
import Data.Maybe
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.State
import Numeric
import Text.Printf

import qualified AST as A
import CompState
import EvalConstants
import EvalLiterals
import Metadata
import Pass
import Errors
import TLP
import Types
import Utils

import GenerateC

--{{{  generator ops
-- | Operations for the C++CSP backend.
-- Most of this can be inherited directly from the C backend.
cppgenOps :: GenOps
cppgenOps = cgenOps {
    declareFree = cppdeclareFree,
    declareInit = cppdeclareInit,
    declareType = cppdeclareType,
    genActual = cppgenActual,
    genActuals = cppgenActuals,
    genArraySubscript = cppgenArraySubscript,
    genDeclType = cppgenDeclType,
    genDeclaration = cppgenDeclaration,
    genFlatArraySize = cppgenFlatArraySize,
    genIf = cppgenIf,
    genInput = cppgenInput,
    genInputCase = cppgenInputCase,
    genInputItem = cppgenInputItem,
    genOutput = cppgenOutput,
    genOutputCase = cppgenOutputCase,
    genOutputItem = cppgenOutputItem,
    genOverArray = cppgenOverArray,
    genPar = cppgenPar,
    genProcCall = cppgenProcCall,
    genSizeSuffix = cppgenSizeSuffix,
    genStop = cppgenStop,
    genTimerRead = cppgenTimerRead,
    genTimerWait = cppgenTimerWait,
    genTopLevel = cppgenTopLevel,
    genType = cppgenType,
    genUnfoldedExpression = cppgenUnfoldedExpression,
    genUnfoldedVariable = cppgenUnfoldedVariable,
    getScalarType = cppgetScalarType,
    introduceSpec = cppintroduceSpec,
    removeSpec = cppremoveSpec
  }
--}}}

{-
For the array handling I am currently using a combination of std::vector and an array view class (tockArrayView) I built myself

I considered the following options:
1. in-built C arrays
2. boost::array
3. std::vector
4. boost::multi_array
5. Blitz++
6. Roll my own.

Option 1 is what Adam used in GenerateC, but it involves carrying around the array sizes, which is a real pain.
Options 2 and 3 are fairly similar (boost::array is possible because arrays are of constant size in occam) but neither supports multiple dimensions
nor array slicing, so that would have been awkward.
Option 4 does support multiple dimensions and array slicing - but the latter would involve keeping tabs of the dimensions of the *original* array
(that was sliced *from*), even through multiple slices and indexes, which would have been a nightmare.
Option 5 makes slicing nice and simple, and multiple dimensions are easy too.  However, things like retyping are still a big problem, so in the end 
it became untenable.

Therefore the only remaining option was 6.  I use std::vector (although this may become boost::array) to actually store each array, and then
use tockArrayView to work with the array.  tockArrayView represents a view of an array, and never allocates or deallocates any memory.  Thus they
can be passed around freely, which makes them easy to work with.

-}

{-
For the ANY type I am currently using boost::any, although knowing *exactly* which type to cast into (and indeed, which type it cast from) is 
problematic so that may have to be reviewed.
-}

{-
For the variant protocols I am using boost::variant.  But when there are more than 9 cases, I have to chain several variants together.
This is perfectly legal C++, but I think it is causing excessive memory usage in g++ (or possibly the tuples....)
-}

{-
For the sequential protocols (including those after a tag in variant protocols) I am using boost::tuple for convenience (along with the handy
boost::tie function to extract the values).  However I suspect this (or the variants -- see above) is causing a lot of memory usage in g++.  Plus,
when more than 9 items are present in the protocol (including variant-tag) I have to chain the tuples together, which means chaining the tie function
as well.  May be worth changing in future
-}

{-
Channels are passed around as pointers to a One2OneChannel<> object.  To read I use the reader() function and to write I use the writer() function.
In occam-pi I could possibly use the channel-ends properly, but in occam 2.1 I have to pass the pointer to the channel itself about the place.
-}


--{{{  top-level
generateCPPCSP :: A.Process -> PassM String
generateCPPCSP = generate cppgenOps

cppgenTopLevel :: GenOps -> A.Process -> CGen ()
cppgenTopLevel ops p
    =  do tell ["#include <tock_support_cppcsp.h>\n"]
          call genProcess ops p
          (name, chans) <- tlpInterface
          tell ["int main (int argc, char** argv) { csp::Start_CPPCSP();"]
          tell ["csp::One2OneChannel<uint8_t> in,out,err;"] --TODO add streamreader
          tell [" csp::Run( csp::InParallel (new StreamWriter(std::cout,out.reader())) (new StreamWriter(std::cerr,err.reader())) (csp::InSequenceOneThread ( new proc_"]
          genName name 
          tell ["("]
          infixComma [tell ["&"] >> call genTLPChannel ops c | c <- chans]
          tell [")) (new csp::common::ChannelPoisoner< csp::Chanout<uint8_t>/**/> (out.writer())) (new csp::common::ChannelPoisoner< csp::Chanout<uint8_t>/**/> (err.writer()))   ) ); csp::End_CPPCSP(); return 0;}"]

--}}}


--CIF has a stop function for stopping processes
--In C++CSP I use the exception handling to make a stop call throw a StopException,
--and the catch is placed so that catching a stop exception immediately finishes the process
cppgenStop :: GenOps -> Meta -> String -> CGen ()
cppgenStop _ m s 
  = do tell ["throw StopException("]
       genMeta m
       tell [" \"",s,"\" );"]

cppgenInput :: GenOps -> A.Variable -> A.InputMode -> CGen ()
cppgenInput ops c im
    =  do t <- typeOfVariable c
          case t of
            A.Timer -> case im of
              A.InputSimple m [A.InVariable m' v] -> call genTimerRead ops c v
              A.InputAfter m e -> call genTimerWait ops e
            _ -> case im of
              A.InputSimple m is -> case t of 
                A.Chan (A.UserProtocol innerType) ->
                  --We read from the channel into a temporary var, then deal with the var afterwards
                  do inputVar <- makeNonce "proto_var"
                     genProtocolName innerType 
                     tell [" ",inputVar, " ; "]
                     call genVariable ops c
                     tell [" ->reader() >> ",inputVar," ; "]
                     cases <- casesOfProtocol innerType
                     genInputTupleAssign ops ((length cases) /= 0) inputVar is
                _ -> sequence_ $ map (call genInputItem ops c) is
              A.InputCase m s -> call genInputCase ops m c s
              _ -> call genMissing ops $ "genInput " ++ show im

cppgenInputCase :: GenOps -> Meta -> A.Variable -> A.Structured -> CGen ()
cppgenInputCase ops m c s 
    = do  t <- typeOfVariable c
          --We have to do complex things with the which() function of the variant (which may be a chained variant)
          --to actually get the real index of the item we have received.
          let proto = case t of A.Chan (A.UserProtocol n) -> n
          tag <- makeNonce "case_tag"          
          which <- makeNonce "which_val"
          genProtocolName proto
          tell [" ", tag, " ; "]
          tell ["unsigned ", which, " ; "]
          call genVariable ops c
          tell [" ->reader() >> ", tag, " ; "]
          whichExpr proto which tag 0 (genProtocolName proto)
          tell [" switch ( ", which, " ) { "]
          genInputCaseBody proto tag (return ()) s
          tell ["default:"]
          call genStop ops m "unhandled variant in CASE input"
          tell ["  } "]
  where
    -- This handles specs in a slightly odd way, because we can't insert specs into
    -- the body of a switch.
    genInputCaseBody :: A.Name -> String -> CGen () -> A.Structured -> CGen ()
    genInputCaseBody proto var coll (A.Spec _ spec s)
        = genInputCaseBody proto var (call genSpec ops spec coll) s
    genInputCaseBody proto var coll (A.OnlyV _ (A.Variant _ n iis p))
        = do protoType <- specTypeOfName proto
             tell ["case ",show (index protoType)," : {"]
             coll
             case iis of
               [] -> return()
               _ ->
                 do caseVar <- genVariantGet proto n var (genProtocolName proto)
                    genInputTupleAssign ops True caseVar iis
             call genProcess ops p
             tell ["break;\n"]
             tell ["}\n"]
             where
               typeList protoType = case protoType of A.ProtocolCase _ types -> types
               index protoType = indexOfTag (typeList protoType) n
    genInputCaseBody proto var coll (A.Several _ ss)
        = sequence_ $ map (genInputCaseBody proto var coll) ss

--This function processes (potentially chained) variants to get the real index of the data item inside the variant
whichExpr :: A.Name -> String -> String -> Int -> CGen() -> CGen()
whichExpr proto which variant offset protoGen
    = do cases <- casesOfProtocol proto 
         case (offset > (length cases)) of
           True -> return ()
           False ->
             do tell [which, " = ", variant , " . which() + ",show offset," ; "]
                case ((offset + 9) > (length cases)) of
                  True -> return ()
                  False ->
                    do tell ["if ( ", which , " == 9 + ",show offset,") { "]
                       innerVariant <- makeNonce "case_tag"                       
                       innerProto
                       tell [" & ",innerVariant," = boost::get< /**/"]
                       innerProto
                       tell [" /**/>( ",variant," ); "]
                       whichExpr proto which innerVariant (offset + 9) innerProto
                       tell [" } "]                    
                       where innerProto = protoGen >> tell ["_"]


--Generates the long boost::tie expression that will be used to get all the data out of a tuple that we have read
genInputTupleAssign :: GenOps -> Bool -> String -> [A.InputItem] -> CGen()
genInputTupleAssign ops hasTag caseVar items
    = do genInputTupleAssign' hasTag caseVar items
         sequence_ $ map genInputSizeAssign items 
  where
    genInputTupleAssign' :: Bool -> String -> [A.InputItem] -> CGen()
    genInputTupleAssign' hasTag caseVar items
      = do  if ((length rest) /= 0) then tell ["tie10("] else tell ["boost::tuples::tie("]
            when (hasTag) (tell ["boost::tuples::ignore,"])
            infixComma (map genInputAssign firstLoad)
            when ((length rest) /= 0) (tell [","] >> genInputTupleAssign' False "" rest)
            if ((length caseVar) /= 0) then tell [") = ",caseVar," ; "] else tell [")"]
        where
          (firstLoad,rest) = splitAt (if hasTag then 8 else 9) items         

    --Gets the variable to input into:
    genInputAssign :: A.InputItem -> CGen()
    genInputAssign (A.InVariable _ arr)
        = call genVariable ops arr
    genInputAssign (A.InCounted _ count arr)
        = call genVariable ops arr

    --Gets the variable that will receieve the size of an inputted array
    genInputSizeAssign :: A.InputItem -> CGen()
    genInputSizeAssign (A.InVariable _ arr)
        = return ()	
    genInputSizeAssign (A.InCounted _ count arr)
        = call genVariable ops count >> tell [" = "] >> call genVariable ops arr >> tell [" .extent(0);"]

--Generates the code for getting a particular tagged value out of a (potentially chained) variant
genVariantGet :: A.Name -> A.Name -> String -> CGen() -> CGen String
genVariantGet proto tag var variantName
    = do cases <- casesOfProtocol proto
         let index = indexOfTag cases tag
         genVariantGet' index proto tag var variantName         
      where
        --This is coded oddly, but it does the job!
        genVariantGet' :: Int -> A.Name -> A.Name -> String -> CGen() -> CGen String
        genVariantGet' index proto tag var variantName
          = do caseVar <- makeNonce "case_tag"
               (target,recur) <- case (index >= 9) of
                 True -> return (variantName >> tell ["_"],genVariantGet' (index - 9) proto tag caseVar (variantName >> tell ["_"]))
                 False -> return (genTupleProtocolTagName proto tag,return caseVar)
               target
               tell [" & ",caseVar," = boost::get< "]
               target
               tell [" >( ", var, " );"]
               recur
      

--C++CSP returns the number of seconds since the epoch as the time
--Since this is too large to be contained in an int once it has been multiplied,
--the remainder is taken to trim the timer back down to something that will be useful in an int
cppgenTimerRead :: GenOps -> A.Variable -> A.Variable -> CGen ()
cppgenTimerRead ops c v
    =  do tell ["csp::CurrentTime (&"]
          call genVariable ops c
          tell [");\n"]
          call genVariable ops v
          tell [" = (int)(unsigned)remainder(1000000.0 * csp::GetSeconds("]
          call genVariable ops c
          tell ["),4294967296.0);\n"]

{-

Time in occam is in microseconds, and is usually stored in the user's programs as a signed 32-bit integer.  Therefore the timer wraps round 
approx every 72 minutes.  A usual pattern of behaviour might be: 

      TIMER tim:
      INT t:
      SEQ
        tim ? t                 -- read current time
        t := t PLUS us          -- add delay
        tim ? AFTER t           -- wait until time "t"

According to Fred's occam page that I took that from, half of time delays are considered in the past and the other half are considered in the future.

Now consider C++CSP's time.  It typically has a more expressive time - on Linux, time is measured since the epoch.  Since the epoch was more 
than 72 minutes ago, this is problematic when converted to microseconds and stuffed into a 32-bit int.  I'll express C++CSP times as (HIGH, LOW) 
where LOW is the lowest 32 bits, and HIGH is the higher bits.

Getting the time for the occam programmer is quite straightforward - we retrieve the C++CSP time, and hand LOW back to the programmer as 
a 32-bit signed value (LOW is unsigned normally).

The occam programmer will now add some delay to their LOW value, making it LOWalpha.  They then ask to wait until LOWalpha.  We know that 
LOWalpha came from LOW at some point in the past and has been added to.  We need to combine it with some HIGH value, HIGHalpha to form 
(HIGHalpha, LOWalpha), the time to wait until.  So what should HIGHalpha be?

We could say that HIGHalpha = HIGH.  But if the user wrapped around LOWalpha, we actually want: HIGHalpha = HIGH + 1.  So we need to check 
if LOWalpha is a wrapped round version of LOW.  This could be done by checking whether LOWalpha < LOW.  If this is true, it must have wrapped.  
Otherwise, it must not have.
-}

--Gets a csp::Time to wait with, given a 32-bit microsecond value (returns the temp variable we have put it in)
genCPPCSPTime :: GenOps -> A.Expression -> CGen String
genCPPCSPTime ops e
    = do  time <- makeNonce "time_exp"
          tell ["unsigned ",time," = (unsigned)"]
          call genExpression ops e
          tell [" ; "]
          curTime <- makeNonce "time_exp"
          curTimeLow <- makeNonce "time_exp"
          curTimeHigh <- makeNonce "time_exp"
          retTime <- makeNonce "time_exp"
          tell ["double ",curTime," = csp::GetSeconds(csp::CurrentTime());"]
          tell ["unsigned ",curTimeLow," = (unsigned)remainder(1000000.0 * ",curTime,",4294967296.0);"]
          tell ["unsigned ",curTimeHigh," = (unsigned)((1000000.0 * ",curTime,") / 4294967296.0);"]
          --if time is less than curTime, it must have wrapped around so add one:
          tell ["csp::Time ",retTime," = csp::Seconds((((double)(",curTimeHigh," + (",time," < ",curTimeLow, " ? 1 : 0)) * 4294967296.0) + (double)",time,") / 1000000.0);"]
          return retTime

cppgenTimerWait :: GenOps -> A.Expression -> CGen ()
cppgenTimerWait ops e
    =  do 
          time <- genCPPCSPTime ops e
          tell ["csp::SleepUntil(",time,");"]

cppgenInputItem :: GenOps -> A.Variable -> A.InputItem -> CGen ()
cppgenInputItem ops c (A.InCounted m cv av)
    =  do call genInputItem ops c (A.InVariable m av)
          --The size is held by the array; we just assign it to the right variable afterwards:
          call genVariable ops cv 
          tell [" = "]
          call genVariable ops av
          tell [" .extent(0); "]
cppgenInputItem ops c (A.InVariable m v)
    =  do    call genVariable ops c
             tell ["->reader() >> "]
             call genVariable ops v
             tell [";\n"]

--If we are sending an array, we use the versionToSend function to coerce away any annoying const tags on the array data:
genJustOutputItem :: GenOps -> A.OutputItem -> CGen()
genJustOutputItem ops (A.OutCounted m ce ae)
    =  do call genExpression ops ae
          tell[" .sliceFor("] 
          call genExpression ops ce 
          tell[") .versionToSend() "]
genJustOutputItem ops (A.OutExpression m e)
    =  do t <- typeOfExpression e
          call genExpression ops e
          case t of
            (A.Array _ _) -> tell [" .versionToSend() "]
            _ -> return ()

cppgenOutputItem :: GenOps -> A.Variable -> A.OutputItem -> CGen ()
cppgenOutputItem ops chan item 
    =  do call genVariable ops chan
          tell [" ->writer() << "]
          genJustOutputItem ops item
          tell [" ; "]

cppgenOutput :: GenOps -> A.Variable -> [A.OutputItem] -> CGen ()
cppgenOutput ops c ois 
    = do t <- typeOfVariable c
         case t of 
           --If it's a protocol, we have to build the appropriate tuple to send down the channel:
           A.Chan (A.UserProtocol innerType) -> 
             do call genVariable ops c
                tell [" ->writer() << "]
                genProtocolName innerType
                tell [" ( "]
                infixComma $ map (genJustOutputItem ops) ois
                tell [" ); "]
           _ -> sequence_ $ map (call genOutputItem ops c) ois

-- FIXME Should be a generic helper somewhere (along with the others from GenerateC)
--Helper function to place a comma between items, but not before or after
infixComma :: [CGen ()] -> CGen ()
infixComma (c0:cs) = c0 >> sequence_ [genComma >> c | c <- cs]
infixComma [] = return ()

--{{{Helper functions for protocol names and tags:

genProtocolName :: A.Name -> CGen()
genProtocolName proto
    = do tell ["protocol_"]
         genName proto

genProtocolTagName :: A.Name -> A.Name -> CGen()
genProtocolTagName proto tag
    = do tell ["protocol_tag_"]
         genName proto
         tell ["_"]
         genName tag

genTupleProtocolTagName :: A.Name -> A.Name -> CGen()
genTupleProtocolTagName proto tag = tell ["tuple_"] >> genProtocolTagName proto tag


--Given a list of cases and a tag, finds the index of that tag:
indexOfTag :: [(A.Name, [A.Type])] -> A.Name -> Int
indexOfTag = indexOfTag' 0
  where
    indexOfTag' :: Int -> [(A.Name, [A.Type])] -> A.Name -> Int
    indexOfTag' n ((possible,_):rest) target
      | possible == target = n
      | otherwise = indexOfTag' (n+1) rest target  

--Helper for getting all the cases of a given protocol:
casesOfProtocol :: A.Name -> CGen [(A.Name, [A.Type])]
casesOfProtocol proto 
    = do protoType <- specTypeOfName proto
         case protoType of 
           A.Protocol _ _ -> return ([])
           A.ProtocolCase _ types -> return (types)

--}}}

--Used when constructing a chained variant -- we must specify the variant types through the chain, so the
--compiler understands that we're giving it one of the inner variants
genSubTypes :: A.Name -> A.Name -> CGen() -> CGen()
genSubTypes proto tag middle 
    =  do protoType <- specTypeOfName proto
          case protoType of
            --sequential, no need for sub-types:
            A.Protocol _ types -> middle
            --choice, do need the sub-types:
            A.ProtocolCase _ types -> do sequence_ 
                                           [ (genProtocolName proto >> 
                                             tell [(replicate ind '_')," ( "]) | ind <- [0 .. byNine]
                                           ]
                                         middle
                                         tell [replicate (byNine + 1) ')']
              --We add one because the protocol tag itself counts as an item in our C++ implementation:
              where realIndex = 1 + (indexOfTag types tag)
                    byNine = realIndex `div` 9
              

cppgenOutputCase :: GenOps -> A.Variable -> A.Name -> [A.OutputItem] -> CGen ()
cppgenOutputCase ops c tag ois 
    =  do t <- typeOfVariable c
          let proto = case t of A.Chan (A.UserProtocol n) -> n
          call genVariable ops c
          tell [" ->writer() << "]
          genSubTypes proto tag (middle proto)
          tell [" ; "]        
          where
            middle proto = tupleExpression True (genTupleProtocolTagName proto tag)  (((genProtocolTagName proto tag) >> tell ["()"]) : map (genJustOutputItem ops) ois)


--We use the process wrappers here, in order to execute the functions in parallel:
--We use forking instead of Run/InParallelOneThread, because it is easier to use forking with replication
cppgenPar :: GenOps -> A.ParMode -> A.Structured -> CGen ()
cppgenPar ops _ s
  = do forking <- makeNonce "forking"
       tell ["{ csp::ScopedForking ",forking," ; "]
       call genStructured ops s (genPar' forking)
       tell [" }"]
       where
         genPar' :: String -> A.Structured -> CGen ()
         genPar' forking (A.OnlyP _ p) 
           = case p of 
             A.ProcCall _ n as -> 
               do tell [forking," .forkInThisThread(new proc_"]
                  genName n
                  tell ["("]
                  call genActuals ops as
                  tell [" ) ); "] 
             _ -> error ("trying to run something other than a process in parallel")
      


--Changed to use C++CSP's Alternative class:
cppgenAlt :: GenOps -> Bool -> A.Structured -> CGen ()
cppgenAlt ops _ s 
  = do guards <- makeNonce "alt_guards"
       tell ["std::list< csp::Guard* > ", guards, " ; "]
       initAltGuards guards s
       alt <- makeNonce "alt"
       tell ["csp::Alternative ",alt, " ( ", guards, " ); "]

       id <- makeNonce "alt_id"
       tell ["int ", id, " = 0;\n"]
       fired <- makeNonce "alt_fired"
       tell ["int ", fired, " = ", alt, " .priSelect();"]
       label <- makeNonce "alt_end"
       tell ["{\n"]
       genAltProcesses id fired label s
       tell ["}\n"]
       tell [label, ":\n;\n"]
  where
    --This function is like the enable function in GenerateC, but this one merely builds a list of guards.  It does not do anything other than add to the guard list
    initAltGuards :: String -> A.Structured -> CGen ()
    initAltGuards guardList s = call genStructured ops s doA
      where
        doA (A.OnlyA _ alt)
            = case alt of
                A.Alternative _ c im _ -> doIn c im
                A.AlternativeCond _ e c im _ -> withIf ops e $ doIn c im
                A.AlternativeSkip _ e _ -> withIf ops e $ tell [guardList, " . push_back( new csp::SkipGuard() );\n"]

        doIn c im
            = do t <- inputType c im
                 case t of
                   ITTimerRead -> call genMissing ops "timer read in ALT"
                   ITTimerAfter ->
                     do let time = case im of A.InputAfter _ e -> e
                        timeVal <- genCPPCSPTime ops time
                        tell [guardList, " . push_back( new csp::TimeoutGuard (",timeVal,"));\n"]
                   ITOther ->
                     do tell [guardList, " . push_back( "]
                        call genVariable ops c
                        tell [" -> reader() . inputGuard());\n"]

    -- This is the same as GenerateC for now -- but it's not really reusable
    -- because it's so closely tied to how ALT is implemented in the backend.
    genAltProcesses :: String -> String -> String -> A.Structured -> CGen ()
    genAltProcesses id fired label s = call genStructured ops s doA
      where
        doA (A.OnlyA _ alt)
            = case alt of
                A.Alternative _ c im p -> doIn c im p
                A.AlternativeCond _ e c im p -> withIf ops e $ doIn c im p
                A.AlternativeSkip _ e p -> withIf ops e $ doCheck (call genProcess ops p)

        doIn c im p
            = do t <- inputType c im
                 case t of
                   ITTimerRead -> call genMissing ops "timer read in ALT"
                   ITTimerAfter -> doCheck (call genProcess ops p)
                   ITOther -> doCheck (call genInput ops c im >> call genProcess ops p)

        doCheck body
            = do tell ["if (", id, "++ == ", fired, ") {\n"]
                 body
                 tell ["goto ", label, ";\n"]
                 tell ["}\n"]


--In GenerateC this uses prefixComma (because "Process * me" is always the first argument), but here we use infixComma:
cppgenActuals :: GenOps -> [A.Actual] -> CGen ()
cppgenActuals ops as = infixComma (map (call genActual ops) as)

--In GenerateC this has special code for passing array sizes around, which we don't need:
cppgenActual :: GenOps -> A.Actual -> CGen ()
cppgenActual ops actual
    = case actual of
        A.ActualExpression t e -> call genExpression ops e
        A.ActualVariable am t v -> cppabbrevVariable ops am t v

--The only change from GenerateC is that passing "me" is not necessary in C++CSP
cppgenProcCall :: GenOps -> A.Name -> [A.Actual] -> CGen ()
cppgenProcCall ops n as 
    = do genName n
         tell ["("]
         call genActuals ops as
         tell [");"]


--Changed from CIF's untyped channels to C++CSP's typed (templated) channels, and changed the declaration type of an array to be a vector:
cppdeclareType :: GenOps -> A.Type -> CGen ()
cppdeclareType ops (A.Array ds t)
    = do tell [" std::vector< "]
         call genType ops t
         tell ["/**/>/**/"]
cppdeclareType ops (A.Counted countType valueType)
    = do tell [" std::vector< "]    
         case valueType of
           --Don't nest when it's a counted array of arrays:
           (A.Array _ t) -> call genType ops t
           _ -> call genType ops valueType
         tell ["/**/>/**/"]
    
cppdeclareType ops (A.Chan t) 
    = do tell [" csp::One2OneChannel < "] 
         call genType ops t 
         tell ["/**/>/**/ "]
cppdeclareType ops t = call genType ops t

--Removed the channel part from GenerateC (not necessary in C++CSP, I think), and also changed the arrays:
--An array is actually stored as a std::vector, but an array-view object is automatically created with the array
--The vector has the suffix _actual, whereas the array-view is what is actually used in place of the array
--I think it may be possible to use boost::array instead of std::vector (which would be more efficient),
--but I will worry about that later
cppgenDeclaration :: GenOps -> A.Type -> A.Name -> CGen ()
cppgenDeclaration ops arrType@(A.Array ds t) n
    =  do call declareType ops arrType
          tell [" "]
          genName n
          tell ["_actual ("]
          call genFlatArraySize ops ds
          tell ["); "]
          call genType ops arrType
          tell [" "]
          genName n;
          tell ["("]
          genName n
          tell ["_actual,tockDims("]
          genDims ds
          tell ["));\n"]
cppgenDeclaration ops t n
    =  do call declareType ops t
          tell [" "]
          genName n
          tell [";\n"]

--Changed because of channel arrays:
cppdeclareInit :: GenOps -> Meta -> A.Type -> A.Variable -> Maybe (CGen ())
cppdeclareInit ops m t@(A.Array ds t') var
    = Just $ do init <- case t' of
                          A.Chan _ ->                    
                               return (\sub -> Just $ do call genVariable ops (sub var)
                                                         tell [" = new "]
                                                         call declareType ops t'
                                                         tell [";\n"]
                                                         doMaybe $ call declareInit ops m t' (sub var))

                          _ -> return (\sub -> call declareInit ops m t' (sub var))
                call genOverArray ops m var init

cppdeclareInit _ _ _ _ = Nothing

--Changed to free channel arrays:
cppdeclareFree :: GenOps -> Meta -> A.Type -> A.Variable -> Maybe (CGen ())
cppdeclareFree ops m t@(A.Array ds t') var
    = Just $ do free <- case t' of
                          A.Chan _ ->                    
                               return (\sub -> Just $ do tell ["delete "]
                                                         call genVariable ops (sub var)
                                                         tell [";\n"]
                                                         --doMaybe $ call declareFree ops m t' (sub var)
                                                         )

                          _ -> return (\sub -> call declareFree ops m t' (sub var))
                call genOverArray ops m var free
                
cppdeclareFree _ _ _ _ = Nothing

--Changed to work properly with declareFree to free channel arrays:
cppremoveSpec :: GenOps -> A.Specification -> CGen ()
cppremoveSpec ops (A.Specification m n (A.Declaration _ t))
    = do case call declareFree ops m t var of
               Just p -> p
               Nothing -> return ()
  where
    var = A.Variable m n
cppremoveSpec _ _ = return ()


-- FIXME: This could be used elsewhere (and work in any monad)
--A helper function that maps a function and calls sequence on the resulting [CGen()]
cgmap :: (t -> CGen()) -> [t] -> CGen()
cgmap func list = sequence_ $ map func list

--Changed from GenerateC because we don't need the extra code for array sizes
cppabbrevExpression :: GenOps -> A.AbbrevMode -> A.Type -> A.Expression -> CGen ()
cppabbrevExpression ops am t@(A.Array _ _) e
    = case e of
        A.ExprVariable _ v -> cppabbrevVariable ops am t v
        A.Literal _ (A.Array ds _) r -> call genExpression ops e
        _ -> bad
  where
    bad = call genMissing ops "array expression abbreviation"
cppabbrevExpression ops am _ e = call genExpression ops e

--Used to create boost::variant and boost::tuple types.  Both these classes can have a maximum of nine items
--so if there are more than nine items, we must have variants containing variants, or tuples containing tuples
createChainedType :: String -> CGen() -> [CGen()] -> CGen ()
createChainedType combinator typeName items
    =  do when ((length rest) /= 0) 
            (createChainedType combinator subName rest)
          tell ["typedef ",combinator," < "]
          infixComma firstNine
          when ((length rest) /= 0)
            (tell [" , "] >> subName)
          --To stop the indent program ruining the C++ Code by combining all the ">" into ">>>" we use these odd blank comments:
          tell ["/**/> "]
          typeName
          tell [" ; "]
       where 
         subName = (typeName >> tell ["_"])
         (firstNine,rest) = splitAt 9 items
         
--Used to create (potentially chained) tuple expressions
tupleExpression :: Bool -> CGen() -> [CGen()] -> CGen()
tupleExpression useBrackets tupleType items
    =  do tupleType
          when (useBrackets) (tell [" ( "])
          infixComma firstNine
          when ((length rest) /= 0) 
            (tell [" , "] >> (tupleExpression True (tell ["boost::make_tuple"]) rest))
          when (useBrackets) (tell [" ) "])
       where 
         (firstNine,rest) = splitAt 9 items

--Takes a list of dimensions and outputs a comma-seperated list of the numerical values
--Unknown dimensions have value 0 (which is treated specially by the tockArrayView class)
genDims:: [A.Dimension] -> CGen()
genDims dims = infixComma $ map genDim dims
  where
    genDim :: A.Dimension -> CGen()
    genDim (A.Dimension n) = tell [show n]
    genDim (A.UnknownDimension) = tell ["0"]

--Generates an expression that yields the number of total elements in a declared multi-dimensional array
--Using it on arrays with unknown dimensions will cause an error (they should only be abbreviations, not declared as actual variables)
cppgenFlatArraySize:: GenOps -> [A.Dimension] -> CGen()
cppgenFlatArraySize ops dims = sequence_ $ intersperse (tell ["*"]) $ map genDim dims
  where
    genDim :: A.Dimension -> CGen()
    genDim (A.Dimension n) = tell [show n]
    genDim dim = call genMissing ops ("No support for dimension: " ++ show dim)

cppintroduceSpec :: GenOps -> A.Specification -> CGen ()
--I generate process wrappers for all functions by default:
cppintroduceSpec ops (A.Specification _ n (A.Proc _ sm fs p))
    =  do --Generate the "process" as a C++ function:
          call genSpecMode ops sm
          tell ["void "]
          name 
          tell [" ("]
          cppgenFormals ops (\x -> x) fs
          tell [") {\n"]
          call genProcess ops p
          tell ["}\n"]                                                                          

          --And generate its CSProcess wrapper:
          tell ["class proc_"]
          name
          tell [" : public csp::CSProcess {private:"]
          genClassVars fs
          tell ["public:inline proc_"]
          name
          tell ["("]
          cppgenFormals ops prefixUnderscore fs
          tell [") : csp::CSProcess(262144)"]
          genConstructorList fs
          tell ["{} protected: virtual void run() { try {"]
          name
          tell [" ( "]
          genParamList fs
          tell [" ); } catch (StopException e) {std::cerr << \"Stopped because: \" << e.reason << std::endl; } } };"]
  where
    name = genName n

    --A simple function for generating declarations of class variables
    genClassVar :: A.Formal -> CGen()
    genClassVar (A.Formal am t n) 
        = do call genDecl ops am t n
             tell[";"]

    --Generates the given list of class variables
    genClassVars :: [A.Formal] -> CGen ()
    genClassVars fs = cgmap genClassVar fs

    --Changed from GenerateC to add a name function (to allow us to use the same function for doing function parameters as constructor parameters)
    --and also changed to use infixComma
    --To use for a constructor list, pass prefixUnderscore as the function, otherwise pass the identity function
    cppgenFormals :: GenOps -> (A.Name -> A.Name) -> [A.Formal] -> CGen ()
    cppgenFormals ops nameFunc list = infixComma (map (cppgenFormal ops nameFunc) list)

    --Changed as genFormals
    cppgenFormal :: GenOps -> (A.Name -> A.Name) -> A.Formal -> CGen ()
    cppgenFormal ops nameFunc (A.Formal am t n) = call genDecl ops am t (nameFunc n)

    --A helper function for generating the initialiser list in a process wrapper constructor
    genConsItem :: A.Formal -> CGen()
    genConsItem (A.Formal am t n)
        = do tell[","]
             genName n
             tell["(_"]
             genName n
             tell[")"]

    --A function for generating the initialiser list in a process wrapper constructor
    genConstructorList :: [A.Formal] -> CGen ()
    genConstructorList fs = cgmap genConsItem fs

    --A helper function for calling the wrapped functions:
    genParam :: A.Formal -> CGen()
    genParam (A.Formal _ _ n) = genName n

    --A helper function for calling the wrapped functions:
    genParamList :: [A.Formal] -> CGen()
    genParamList fs = infixComma $ map genParam fs

-- FIXME: We could just fall through to cintroduceSpec as the last clause...
--This clause is unchanged from GenerateC:
cppintroduceSpec ops (A.Specification m n (A.Declaration _ t))
    = do call genDeclaration ops t n
         case call declareInit ops m t (A.Variable m n) of
           Just p -> p
           Nothing -> return ()
--This clause is unchanged from GenerateC:
cppintroduceSpec ops (A.Specification _ n (A.Is _ am t v))
    =  do let rhs = cppabbrevVariable ops am t v
          call genDecl ops am t n
          tell [" = "]
          rhs
          tell [";\n"]
--Clause only changed to use Blitz++ rather than C arrays:
cppintroduceSpec ops (A.Specification _ n (A.IsExpr _ am t e))
    =  do let rhs = cppabbrevExpression ops am t e
          case (am, t, e) of
            (A.ValAbbrev, A.Array _ ts, A.Literal _ (A.Array dims _)  _) ->
              -- For "VAL []T a IS [vs]:", we have to use [] rather than * in the
              -- declaration, since you can't say "int *foo = {vs};" in C.
              do tmp <- makeNonce "array_literal"
                 tell ["const "]
                 call genType ops ts
                 tell [" ",tmp, " [] = "]
                 rhs
                 tell [" ; "]
                 tell ["const tockArrayView< const "]
                 call genType ops ts
                 tell [" , ",show (length dims)," /**/>/**/ "]
                 genName n
                 tell ["(("]
                 call genType ops ts 
                 tell [" *)",tmp,",tockDims("]
                 genDims dims
                 tell ["));\n"]
            (A.ValAbbrev, A.Record _, A.Literal _ _ _) ->
              -- Record literals are even trickier, because there's no way of
              -- directly writing a struct literal in C that you can use -> on.
              do tmp <- makeNonce "record_literal"
                 tell ["const "]
                 call genType ops t
                 tell [" ", tmp, " = "]
                 rhs
                 tell [";\n"]
                 call genDecl ops am t n
                 tell [" = &", tmp, ";\n"]
            _ ->
              do call genDecl ops am t n
                 tell [" = "]
                 rhs
                 tell [";\n"]

--We must create the channel array then fill it:
cppintroduceSpec ops (A.Specification _ n (A.IsChannelArray _ t cs))
    =  do call genDeclaration ops t n
          sequence_ $ map genChanArrayElemInit (zip [0 .. ((length cs) - 1)] cs)
          where
            genChanArrayElemInit (index,var)
              = do genName n
                   tell ["[",show index,"].access() = "] --Use the .access() function to cast a 0-dimension array into a T& for access
                   call genVariable ops var
                   tell [";"]
--This clause is unchanged from GenerateC:
cppintroduceSpec _ (A.Specification _ _ (A.DataType _ _)) = return ()
--This clause was simplified, because the array handling could be removed:
cppintroduceSpec ops (A.Specification _ n (A.RecordType _ b fs))
    =  do tell ["typedef struct {\n"]
          sequence_ [call genDeclaration ops t n
                     | (n, t) <- fs]
          tell ["} "]
          when b $ tell ["occam_struct_packed "]
          genName n
          tell [";\n"]
--We do sequential protocols by introducing a new tuple:
cppintroduceSpec ops (A.Specification _ n (A.Protocol _ typeList))
    =  do createChainedType "boost::tuple" (genProtocolName n) $ map (call genType ops) typeList
--We do variant protocols by introducing a new variant:
cppintroduceSpec _ (A.Specification _ n (A.ProtocolCase _ []))
    =  do tell ["typedef class {} "] 
          genName n
          tell [";"]
cppintroduceSpec ops (A.Specification _ n (A.ProtocolCase _ caseList))
    =  do sequence_ [tell ["class "] >> genProtocolTagName n tag >> tell [" {}; "] | (tag , _) <- caseList]    
          cgmap (typedef_genCaseType n) caseList          
          createChainedType "boost::variant" (genProtocolName n) $ map ((genTupleProtocolTagName n) . fst) caseList
          where 
            typedef_genCaseType :: A.Name -> (A.Name, [A.Type]) -> CGen()
            typedef_genCaseType n (tag, typeList) 
              =  createChainedType "boost::tuple" (genTupleProtocolTagName n tag) ((genProtocolTagName n tag) : (map (call genType ops) typeList))
          
--Clause changed to handle array retyping
cppintroduceSpec ops (A.Specification _ n (A.Retypes m am t v))
    =  do origT <- typeOfVariable v
          let rhs = cppabbrevVariable ops A.Abbrev origT v
          call genDecl ops am t n
          tell [" = "]
          case t of 
            (A.Array dims _) ->
              --Arrays need to be handled differently because we need to feed the sizes in, not just perform a straight cast
              do call genDeclType ops am t
                 tell ["("]
                 rhs
                 tell [",tockDims("]
                 genDims dims
                 tell ["));"]            
            _ ->      
              -- For scalar types that are VAL abbreviations (e.g. VAL INT64),
              -- we need to dereference the pointer that cppabbrevVariable gives us.
              do let deref = case (am, t) of
                               (_, A.Array _ _) -> False
                               (_, A.Chan _) -> False
                               (A.ValAbbrev, _) -> True
                               _ -> False
                 when deref $ tell ["*"]
                 tell ["("]
                 call genDeclType ops am t
                 when deref $ tell [" *"]
                 tell [") ("]
                 rhs                 
                 case origT of 
                     --We must be retyping from an array, but not to an array (so to a primitive type or something):
                   (A.Array _ _) -> tell [".data()"]
                   _ -> return ()
                 tell [");\n"]

--This clause is unchanged from GenerateC:
cppintroduceSpec ops n = call genMissing ops $ "introduceSpec " ++ show n

cppgenSizeSuffix :: GenOps -> String -> CGen ()
cppgenSizeSuffix _ dim = tell [".extent(", dim, ")"]
--}}}


--{{{  types
-- | If a type maps to a simple C type, return Just that; else return Nothing.

--Changed from GenerateC to change the A.Timer type to use C++CSP time
--Also changed the bool type, because vector<bool> in C++ is odd, so we hide it from the compiler:
cppgetScalarType :: GenOps -> A.Type -> Maybe String
cppgetScalarType _ A.Bool = Just "tockBool"
cppgetScalarType _ A.Byte = Just "uint8_t"
cppgetScalarType _ A.Int = Just "int"
cppgetScalarType _ A.Int16 = Just "int16_t"
cppgetScalarType _ A.Int32 = Just "int32_t"
cppgetScalarType _ A.Int64 = Just "int64_t"
cppgetScalarType _ A.Real32 = Just "float"
cppgetScalarType _ A.Real64 = Just "double"
cppgetScalarType _ A.Timer = Just "csp::Time"
cppgetScalarType _ _ = Nothing

--Generates an array type, giving the Blitz++ array the correct dimensions
cppgenArrayType :: GenOps -> Bool -> A.Type -> Int -> CGen ()
cppgenArrayType ops const (A.Array dims t) rank
    =  cppgenArrayType ops const t (rank + (max 1 (length dims)))
cppgenArrayType ops const t rank
    =  do tell [" tockArrayView< "]
          when (const) (tell [" const "])
          call genType ops t
          tell [" , ",show rank, " > /**/"]
    
--Changed from GenerateC to change the arrays and the channels
--Also changed to add counted arrays and user protocols
cppgenType :: GenOps -> A.Type -> CGen ()
cppgenType ops arr@(A.Array _ _)
    =  cppgenArrayType ops False arr 0    
cppgenType _ (A.Record n) = genName n
cppgenType _ (A.UserProtocol n) = genProtocolName n
cppgenType ops (A.Chan t) 
    = do tell ["csp::One2OneChannel < "]
         call genType ops t
         tell [" > * "]
cppgenType ops (A.Counted countType valueType)
    = call genType ops (A.Array [A.UnknownDimension] valueType)
cppgenType _ (A.Any)
    = tell [" tockAny "]
-- Any -- not used
--cppgenType (A.Port t) =
cppgenType ops t
    = case call getScalarType ops t of
        Just s -> tell [s]
        Nothing -> call genMissing ops $ "genType " ++ show t


--Helper function for prefixing an underscore (looks like fairly ugly Haskell - maybe there is an easier way?)
-- FIXME: Yes, there is
prefixUnderscore :: A.Name -> A.Name
prefixUnderscore n = A.Name {A.nameMeta = A.nameMeta n, A.nameType = A.nameType n, A.nameName = "_" ++ A.nameName n}


-- | Generate the right-hand side of an abbreviation of a variable.
--Changed from GenerateC because we no longer need the A.Name -> CGen() function returned that dealt with array sizes
--I also pass the type of the array through to cppgenSlice
cppabbrevVariable :: GenOps -> A.AbbrevMode -> A.Type -> A.Variable -> CGen ()
cppabbrevVariable ops am (A.Array _ _) v@(A.SubscriptedVariable _ (A.Subscript _ _) _)
    = cppgenArrayAbbrev ops v
cppabbrevVariable ops am ty@(A.Array ds _) v@(A.SubscriptedVariable _ (A.SubscriptFromFor _ start count) v')
    = cppgenSlice ops v v' ty start count ds
cppabbrevVariable ops am ty@(A.Array ds _) v@(A.SubscriptedVariable m (A.SubscriptFrom _ start) v')
    = cppgenSlice ops v v' ty start (A.Dyadic m A.Minus (A.SizeExpr m (A.ExprVariable m v')) start) ds
cppabbrevVariable ops am ty@(A.Array ds _) v@(A.SubscriptedVariable m (A.SubscriptFor _ count) v')
    = cppgenSlice ops v v' ty (makeConstant m 0) count ds
cppabbrevVariable ops am (A.Array _ _) v
    = call genVariable ops v
cppabbrevVariable ops am (A.Chan _) v
    = call genVariable ops v
cppabbrevVariable ops am (A.Record _) v
    = call genVariable ops v
cppabbrevVariable ops am t v
    = call genVariableAM ops v am


--Use C++ array slices:
--TODO put index checking back:
cppgenSlice :: GenOps -> A.Variable -> A.Variable -> A.Type -> A.Expression -> A.Expression -> [A.Dimension] -> CGen ()
cppgenSlice ops _ v ty start count ds
       -- We need to disable the index check here because we might be taking
       -- element 0 of a 0-length array -- which is valid.
    = do  call genVariableUnchecked ops v
          tell [".sliceFromFor("]        
          call genExpression ops start
          tell [" , "]
          call genExpression ops count
          tell [")"]          
         

--Removed the sizing and the & from GenerateC:
cppgenArrayAbbrev :: GenOps -> A.Variable -> CGen ()
cppgenArrayAbbrev = call genVariable


--Changed from GenerateC to use Blitz++ subscripting (round brackets with commas) rather than traditional C indexing
cppgenArraySubscript :: GenOps -> Bool -> A.Variable -> [A.Expression] -> CGen ()
cppgenArraySubscript ops checkValid v es
    =  do t <- typeOfVariable v
          let numDims = case t of A.Array ds _ -> length ds
          sequence_ $ genPlainSub v es [0..(numDims - 1)]
  where
    -- | Generate the individual offsets that need adding together to find the
    -- right place in the array.
    -- FIXME This is obviously not the best way to factor this, but I figure a
    -- smart C compiler should be able to work it out...
    
    --Subtly changed this function so that empty dimensions have blitz::Range::all() in the C++ version:
    --TODO doc
    
    genPlainSub :: A.Variable -> [A.Expression] -> [Int] -> [CGen ()]
    genPlainSub _ _ [] = []
    genPlainSub v [] (sub:subs) = (tell [" "]) : (genPlainSub v [] subs)
    genPlainSub v (e:es) (sub:subs)
        = (tell ["["] >> genSub >> tell ["]"]) : genPlainSub v es subs
      where
        genSub
            = if checkValid
                then do tell ["occam_check_index ("]
                        call genExpression ops e
                        tell [", "]
                        call genVariable ops v
                        tell [".extent(", show sub, "), "]
                        genMeta (findMeta e)
                        tell [")"]
                else call genExpression ops e
--}}}

-- | Map an operation over every item of an occam array.
--Changed from GenerateC because it uses the array sizes of Blitz++
cppgenOverArray :: GenOps -> Meta -> A.Variable -> (SubscripterFunction -> Maybe (CGen ())) -> CGen ()
cppgenOverArray ops m var func
    =  do A.Array ds _ <- typeOfVariable var
          specs <- sequence [makeNonceVariable "i" m A.Int A.VariableName A.Original | _ <- ds]
          let indices = [A.Variable m n | A.Specification _ n _ <- specs]

          let arg = (\var -> foldl (\v s -> A.SubscriptedVariable m s v) var [A.Subscript m $ A.ExprVariable m i | i <- indices])
          case func arg of
            Just p ->
              do sequence_ [do tell ["for (int "]
                               call genVariable ops i
                               tell [" = 0; "]
                               call genVariable ops i
                               tell [" < "]
                               call genVariable ops var
                               tell [".extent(", show v, "); "]
                               call genVariable ops i
                               tell ["++) {\n"]
                            | (v, i) <- zip [0..] indices]
                 p
                 sequence_ [tell ["}\n"] | _ <- indices]
            Nothing -> return ()



--Changed to remove array size:
cppgenUnfoldedExpression :: GenOps -> A.Expression -> CGen ()
cppgenUnfoldedExpression ops (A.Literal _ t lr)
    =  call genLiteralRepr ops lr
cppgenUnfoldedExpression ops (A.ExprVariable m var) = call genUnfoldedVariable ops m var
cppgenUnfoldedExpression ops e = call genExpression ops e

--Changed to remove array size:
cppgenUnfoldedVariable :: GenOps -> Meta -> A.Variable -> CGen ()
cppgenUnfoldedVariable ops m var
    =  do t <- typeOfVariable var
          case t of
            A.Array ds _ ->
              do genLeftB
                 unfoldArray ds var
                 genRightB
            A.Record _ ->
              do genLeftB
                 fs <- recordFields m t
                 seqComma [call genUnfoldedVariable ops m (A.SubscriptedVariable m (A.SubscriptField m n) var)
                           | (n, t) <- fs]
                 genRightB
            -- We can defeat the usage check here because we know it's safe; *we're*
            -- generating the subscripts.
            -- FIXME Is that actually true for something like [a[x]]?
            _ -> call genVariable' ops False var
  where
    unfoldArray :: [A.Dimension] -> A.Variable -> CGen ()
    unfoldArray [] v = call genUnfoldedVariable ops m v
    unfoldArray (A.Dimension n:ds) v
      = seqComma $ [unfoldArray ds (A.SubscriptedVariable m (A.Subscript m $ makeConstant m i) v)
                    | i <- [0..(n - 1)]]
    unfoldArray _ _ = dieP m "trying to unfold array with unknown dimension"


--{{{  if
--Changed to throw a nonce-exception class instead of the goto, because C++ doesn't allow gotos to cross class initialisations (such as arrays)

cppgenIf :: GenOps -> Meta -> A.Structured -> CGen ()
cppgenIf ops m s
    =  do ifExc <- makeNonce "if_exc"
          tell ["class ",ifExc, " {}; try {"]
          genIfBody ifExc s
          call genStop ops m "no choice matched in IF process"
          tell ["} catch (",ifExc,") {}"]
  where
    genIfBody :: String -> A.Structured -> CGen ()
    genIfBody ifExc s = call genStructured ops s doC
      where
        doC (A.OnlyC m (A.Choice m' e p))
            = do tell ["if ("]
                 call genExpression ops e
                 tell [") {\n"]
                 call genProcess ops p
                 tell ["throw ",ifExc, "(); }\n"]
--}}}


--Changed to make array VAL abbreviations have constant data:
cppgenDeclType :: GenOps -> A.AbbrevMode -> A.Type -> CGen ()
cppgenDeclType ops am t
    =  do case t of
            A.Array _ _ -> cppgenArrayType ops (am == A.ValAbbrev) t 0
            _ ->
              do when (am == A.ValAbbrev) $ tell ["const "]
                 call genType ops t
                 case t of
                   A.Chan _ -> return ()
                   A.Record _ -> tell [" *"]
                   _ -> when (am == A.Abbrev) $ tell [" *"]


