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

import GenerateC (CGen,genName,genMeta,missing,genComma,genIntrinsicProc,genBytesIn,genTLPChannel,genDecimal,
  genLeftB,genRightB,seqComma,isStringLiteral,genByteLiteral,genTypeSymbol,isZero,genSpecMode,SubscripterFunction)

{-
Much of this file is influenced by, or taken from, GenerateC.

Typically there were two reasons to copy code from GenerateC, rather than simply import it:
1. To change the actual behaviour (for example, using C++CSP timers rather than CIF timers)
2. To recurse into my C++CSP generating code rather than C generating code, but otherwise not changing the behaviour

Reason 1 is obviously necessary - I need to change the CIF calls into C++CSP, and I can also changed some of the C (such as the arrays) into C++.

Reason 2 is annoying - the code remains the same in both GenerateC and this GenerateCPPCSP module, but I have to move it over so that calls
to other functions use my GenerateCPPCSP versions and not GenerateC versions.
For example, genProcess is identical in GenerateC and GenerateCPPCSP, but in this file it calls (e.g.) GenerateCPPCSP.genInput rather than
GenerateC.genInput.  I can't see any easy way to fix this, other than carrying around a dictionary of functions to be called, but that seems
like more hassle than just duplicating the code.

Code that has been imported verbatim from GenerateC (reason 2) has been tagged accordingly.  Assume all other functions are here for reason 1.

-}


{-
For the array handling I am currently using the Blitz++ library: http://www.oonumerics.org/blitz/

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
(that was sliced *from*), even through multiple slices, which would have been a nightmare.
Option 5 makes slicing nice and simple, and multiple dimensions are easy too.  Hence, although it adds another dependency (boost would not have counted, 
as it is already a dependency of C++CSP) it is definitely the easiest solution for code generation.  The dependency could be removed through option 6
(even to the point of taking some GPL Blitz++ code) but that seems a step too far just to remove a dependency.

ADDENDUM: I have wrapped blitz::Array into tockArray in order to make the assignment work correctly (resizing before copy) and also provide
some useful constructors

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
generateCPPCSP ast
    =  do (a, w) <- runWriterT (genTopLevel ast)
          return $ concat w

genTopLevel :: A.Process -> CGen ()
genTopLevel p
    =  do tell ["#include <tock_support_cppcsp.h>\n"]
          genProcess p
          (name, chans) <- tlpInterface
          tell ["int main (int argc, char** argv) { csp::Start_CPPCSP();"]
          tell ["csp::One2OneChannel<uint8_t> in,out,err;"] --TODO add streamreader
          tell [" csp::Run( csp::InParallel (new StreamWriter(std::cout,out.reader())) (new StreamWriter(std::cerr,err.reader())) (csp::InSequenceOneThread ( new proc_"]
          genName name 
          tell ["("]
          infixComma [tell ["&"] >> genTLPChannel c | c <- chans]
          tell [")) (new csp::common::ChannelPoisoner< csp::Chanout<uint8_t>/**/> (out.writer())) (new csp::common::ChannelPoisoner< csp::Chanout<uint8_t>/**/> (err.writer()))   ) ); csp::End_CPPCSP(); return 0;}"]

--}}}


--CIF has a stop function for stopping processes
--In C++CSP I use the exception handling to make a stop call throw a StopException,
--and the catch is placed so that catching a stop exception immediately finishes the process
genStop :: Meta -> String -> CGen ()
genStop m s 
  = do tell ["throw StopException("]
       genMeta m
       tell [" \"",s,"\" );"]


genInput :: A.Variable -> A.InputMode -> CGen ()
genInput c im
    =  do t <- typeOfVariable c
          case t of
            A.Timer -> case im of
              A.InputSimple m [A.InVariable m' v] -> genTimerRead c v
              A.InputAfter m e -> genTimerWait e
            _ -> case im of
              A.InputSimple m is -> case t of 
                A.Chan (A.UserProtocol innerType) ->
                  --We read from the channel into a temporary var, then deal with the var afterwards
                  do inputVar <- makeNonce "proto_var"
                     genProtocolName innerType 
                     tell [" ",inputVar, " ; "]
                     genVariable c
                     tell [" ->reader() >> ",inputVar," ; "]
                     cases <- casesOfProtocol innerType
                     genInputTupleAssign ((length cases) /= 0) inputVar is
                _ -> sequence_ $ map (genInputItem c) is
              A.InputCase m s -> genInputCase m c s
              _ -> missing $ "genInput " ++ show im

genInputCase :: Meta -> A.Variable -> A.Structured -> CGen ()
genInputCase m c s 
    = do  t <- typeOfVariable c
          --We have to do complex things with the which() function of the variant (which may be a chained variant)
          --to actually get the real index of the item we have received.
          let proto = case t of A.Chan (A.UserProtocol n) -> n
          tag <- makeNonce "case_tag"          
          which <- makeNonce "which_val"
          genProtocolName proto
          tell [" ", tag, " ; "]
          tell ["unsigned ", which, " ; "]
          genVariable c
          tell [" ->reader() >> ", tag, " ; "]
          whichExpr proto which tag 0 (genProtocolName proto)
          tell [" switch ( ", which, " ) { "]
          genInputCaseBody proto tag (return ()) s
          tell ["default:"]
          genStop m "unhandled variant in CASE input"
          tell ["  } "]

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


--Gets the variable to input into:
genInputAssign :: A.InputItem -> CGen()
genInputAssign (A.InVariable _ arr)
    = genVariable arr
genInputAssign (A.InCounted _ count arr)
    = genVariable arr

--Gets the variable that will receieve the size of an inputted array
genInputSizeAssign :: A.InputItem -> CGen()
genInputSizeAssign (A.InVariable _ arr)
    = return ()	
genInputSizeAssign (A.InCounted _ count arr)
    = genVariable count >> tell [" = "] >> genVariable arr >> tell [" .extent(0);"]

--Generates the long boost::tie expression that will be used to get all the data out of a tuple that we have read
genInputTupleAssign :: Bool -> String -> [A.InputItem] -> CGen()
genInputTupleAssign hasTag caseVar items
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
      

-- This handles specs in a slightly odd way, because we can't insert specs into
-- the body of a switch.
genInputCaseBody :: A.Name -> String -> CGen () -> A.Structured -> CGen ()
genInputCaseBody proto var coll (A.Spec _ spec s)
    = genInputCaseBody proto var (genSpec spec coll) s
genInputCaseBody proto var coll (A.OnlyV _ (A.Variant _ n iis p))
    = do protoType <- specTypeOfName proto
         tell ["case ",show (index protoType)," : {"]
         coll
         case iis of
           [] -> return()
           _ ->
             do caseVar <- genVariantGet proto n var (genProtocolName proto)
                genInputTupleAssign True caseVar iis
         genProcess p
         tell ["break;\n"]
         tell ["}\n"]
         where
           typeList protoType = case protoType of A.ProtocolCase _ types -> types
           index protoType = indexOfTag (typeList protoType) n

      
genInputCaseBody proto var coll (A.Several _ ss)
    = sequence_ $ map (genInputCaseBody proto var coll) ss

--C++CSP returns the number of seconds since the epoch as the time
--Since this is too large to be contained in an int once it has been multiplied,
--the remainder is taken to trim the timer back down to something that will be useful in an int
genTimerRead :: A.Variable -> A.Variable -> CGen ()
genTimerRead c v
    =  do tell ["csp::CurrentTime (&"]
          genVariable c
          tell [");\n"]
          genVariable v
          tell [" = (int)(unsigned)remainder(1000000.0 * csp::GetSeconds("]
          genVariable c
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
genCPPCSPTime :: A.Expression -> CGen String
genCPPCSPTime e
    = do  time <- makeNonce "time_exp"
          tell ["unsigned ",time," = (unsigned)"]
          genExpression e
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

genTimerWait :: A.Expression -> CGen ()
genTimerWait e
    =  do 
          time <- genCPPCSPTime e
          tell ["csp::SleepUntil(",time,");"]

genInputItem :: A.Variable -> A.InputItem -> CGen ()
genInputItem c (A.InCounted m cv av)
    =  do genInputItem c (A.InVariable m av)
          --The size is held by the array; we just assign it to the right variable afterwards:
          genVariable cv 
          tell [" = "]
          genVariable av
          tell [" .extent(0); "]
genInputItem c (A.InVariable m v)
    =  do    genVariable c
             tell ["->reader() >> "]
             genVariable v
             tell [";\n"]

--If we are sending an array, we use the versionToSend function to coerce away any annoying const tags on the array data:
genJustOutputItem :: A.OutputItem -> CGen()
genJustOutputItem (A.OutCounted m ce ae)
    =  do genExpression ae
          tell[" .sliceFor("] 
          genExpression ce 
          tell[") .versionToSend() "]
genJustOutputItem (A.OutExpression m e)
    =  do t <- typeOfExpression e
          genExpression e
          case t of
            (A.Array _ _) -> tell [" .versionToSend() "]
            _ -> return ()

genOutputItem :: A.Variable -> A.OutputItem -> CGen ()
genOutputItem chan item 
    =  do genVariable chan
          tell [" ->writer() << "]
          genJustOutputItem item
          tell [" ; "]

genOutput :: A.Variable -> [A.OutputItem] -> CGen ()
genOutput c ois 
    = do t <- typeOfVariable c
         case t of 
           --If it's a protocol, we have to build the appropriate tuple to send down the channel:
           A.Chan (A.UserProtocol innerType) -> 
             do genVariable c
                tell [" ->writer() << "]
                genProtocolName innerType
                tell [" ( "]
                infixComma $ map genJustOutputItem ois
                tell [" ); "]
           _ -> sequence_ $ map (genOutputItem c) ois

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
              

genOutputCase :: A.Variable -> A.Name -> [A.OutputItem] -> CGen ()
genOutputCase c tag ois 
    =  do t <- typeOfVariable c
          let proto = case t of A.Chan (A.UserProtocol n) -> n
          genVariable c
          tell [" ->writer() << "]
          genSubTypes proto tag (middle proto)
          tell [" ; "]        
          where
            middle proto = tupleExpression True (genTupleProtocolTagName proto tag)  (((genProtocolTagName proto tag) >> tell ["()"]) : map genJustOutputItem ois)


--We use the process wrappers here, in order to execute the functions in parallel:
--We use forking instead of Run/InParallelOneThread, because it is easier to use forking with replication
genPar :: A.ParMode -> A.Structured -> CGen ()
genPar _ s 
  = do forking <- makeNonce "forking"
       tell ["{ csp::ScopedForking ",forking," ; "]
       genStructured s (genPar' forking)
       tell [" }"]
       where
         genPar' :: String -> A.Structured -> CGen ()
         genPar' forking (A.OnlyP _ p) 
           = case p of 
             A.ProcCall _ n as -> 
               do tell [forking," .forkInThisThread(new proc_"]
                  genName n
                  tell ["("]
                  genActuals as
                  tell [" ) ); "] 
             _ -> error ("trying to run something other than a process in parallel")
      


--Changed to use C++CSP's Alternative class:
genAlt :: Bool -> A.Structured -> CGen ()
genAlt _ s 
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

--This function is like the enable function in GenerateC, but this one merely builds a list of guards.  It does not do anything other than add to the guard list
initAltGuards :: String -> A.Structured -> CGen ()
initAltGuards guardList s = genStructured s doA
  where
    doA (A.OnlyA _ alt)
        = case alt of
            A.Alternative _ c im _ -> doIn c im
            A.AlternativeCond _ e c im _ -> withIf e $ doIn c im
            A.AlternativeSkip _ e _ -> withIf e $ tell [guardList, " . push_back( new csp::SkipGuard() );\n"]

    doIn c im
        = do t <- inputType c im
             case t of
               ITTimerRead -> missing "timer read in ALT"
               ITTimerAfter ->
                 do let time = case im of A.InputAfter _ e -> e
                    timeVal <- genCPPCSPTime time
                    tell [guardList, " . push_back( new csp::TimeoutGuard (",timeVal,"));\n"]
               ITOther ->
                 do tell [guardList, " . push_back( "]
                    genVariable c
                    tell [" -> reader() . inputGuard());\n"]

--In GenerateC this uses prefixComma (because "Process * me" is always the first argument), but here we use infixComma:
genActuals :: [A.Actual] -> CGen ()
genActuals as = infixComma (map genActual as)

--In GenerateC this has special code for passing array sizes around, which we don't need:
genActual :: A.Actual -> CGen ()
genActual actual
    = case actual of
        A.ActualExpression t e -> genExpression e
        A.ActualVariable am t v -> abbrevVariable am t v

--The only change from GenerateC is that passing "me" is not necessary in C++CSP
genProcCall :: A.Name -> [A.Actual] -> CGen ()
genProcCall n as 
    = do genName n
         tell ["("]
         genActuals as
         tell [");"]


--Changed from CIF's untyped channels to C++CSP's typed (templated) channels, and changed the declaration type of an array to be a vector:
declareType :: A.Type -> CGen ()
declareType (A.Array ds t)
    = do tell [" std::vector< "]
         genType t
         tell ["/**/>/**/"]
declareType (A.Counted countType valueType)
    = do tell [" std::vector< "]    
         case valueType of
           --Don't nest when it's a counted array of arrays:
           (A.Array _ t) -> genType t
           _ -> genType valueType
         tell ["/**/>/**/"]
    
declareType (A.Chan t) 
    = do tell [" csp::One2OneChannel < "] 
         genType t 
         tell ["/**/>/**/ "]
declareType t = genType t

--Removed the channel part from GenerateC (not necessary in C++CSP, I think), and also changed the arrays:
--An array is actually stored as a std::vector, but an array-view object is automatically created with the array
--The vector has the suffix _actual, whereas the array-view is what is actually used in place of the array
--I think it may be possible to use boost::array instead of std::vector (which would be more efficient),
--but I will worry about that later
genDeclaration :: A.Type -> A.Name -> CGen ()
genDeclaration arrType@(A.Array ds t) n
    =  do declareType arrType
          tell [" "]
          genName n
          tell ["_actual ("]
          genFlatArraySize ds
          tell ["); "]
          genType arrType
          tell [" "]
          genName n;
          tell ["("]
          genName n
          tell ["_actual,tockDims("]
          genDims ds
          tell ["));\n"]
genDeclaration t n
    =  do declareType t
          tell [" "]
          genName n
          tell [";\n"]

--Changed because of channel arrays:
declareInit :: Meta -> A.Type -> A.Variable -> Maybe (CGen ())
declareInit m t@(A.Array ds t') var
    = Just $ do init <- case t' of
                          A.Chan _ ->                    
                               return (\sub -> Just $ do genVariable (sub var)
                                                         tell [" = new "]
                                                         declareType t'
                                                         tell [";\n"]
                                                         doMaybe $ declareInit m t' (sub var))

                          _ -> return (\sub -> declareInit m t' (sub var))
                overArray m var init

declareInit _ _ _ = Nothing

--Changed to free channel arrays:
declareFree :: Meta -> A.Type -> A.Variable -> Maybe (CGen ())

declareFree m t@(A.Array ds t') var
    = Just $ do free <- case t' of
                          A.Chan _ ->                    
                               return (\sub -> Just $ do tell ["delete "]
                                                         genVariable (sub var)
                                                         tell [";\n"]
                                                         --doMaybe $ declareFree m t' (sub var)
                                                         )

                          _ -> return (\sub -> declareFree m t' (sub var))
                overArray m var free
                
declareFree _ _ _ = Nothing

--Changed to work properly with declareFree to free channel arrays:
removeSpec :: A.Specification -> CGen ()
removeSpec (A.Specification m n (A.Declaration _ t))
    = do case declareFree m t var of
               Just p -> p
               Nothing -> return ()
  where
    var = A.Variable m n
removeSpec _ = return ()


--A helper function that maps a function and calls sequence on the resulting [CGen()]
cgmap :: (t -> CGen()) -> [t] -> CGen()
cgmap func list = sequence_ $ map func list

--A simple function for generating declarations of class variables
genClassVar :: A.Formal -> CGen()
genClassVar (A.Formal am t n) 
    = do genDecl am t n
         tell[";"]

--Generates the given list of class variables
genClassVars :: [A.Formal] -> CGen ()
genClassVars fs = cgmap genClassVar fs

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

--Changed from GenerateC because we don't need the extra code for array sizes
abbrevExpression :: A.AbbrevMode -> A.Type -> A.Expression -> CGen ()
abbrevExpression am t@(A.Array _ _) e
    = case e of
        A.ExprVariable _ v -> abbrevVariable am t v
        A.Literal _ (A.Array ds _) r -> genExpression e
        _ -> bad
  where
    bad = missing "array expression abbreviation"
abbrevExpression am _ e = genExpression e

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
genFlatArraySize:: [A.Dimension] -> CGen()
genFlatArraySize dims = sequence_ $ intersperse (tell ["*"]) $ map genDim dims
  where
    genDim :: A.Dimension -> CGen()
    genDim (A.Dimension n) = tell [show n]
    genDim dim = missing ("No support for dimension: " ++ show dim)

introduceSpec :: A.Specification -> CGen ()
--I generate process wrappers for all functions by default:
introduceSpec (A.Specification _ n (A.Proc _ sm fs p))
    =  do --Generate the "process" as a C++ function:
          genSpecMode sm
          tell ["void "]
          name 
          tell [" ("]
          genFormals (\x -> x) fs
          tell [") {\n"]
          genProcess p
          tell ["}\n"]                                                                          

          --And generate its CSProcess wrapper:
          tell ["class proc_"]
          name
          tell [" : public csp::CSProcess {private:"]
          genClassVars fs
          tell ["public:inline proc_"]
          name
          tell ["("]
          genFormals prefixUnderscore fs
          tell [") : csp::CSProcess(65536)"]
          genConstructorList fs
          tell ["{} protected: virtual void run() { try {"]
          name
          tell [" ( "]
          genParamList fs
          tell [" ); } catch (StopException e) {std::cerr << \"Stopped because: \" << e.reason << std::endl; } } };"]
       where name = genName n
--This clause is unchanged from GenerateC:
introduceSpec (A.Specification m n (A.Declaration _ t))
    = do genDeclaration t n
         case declareInit m t (A.Variable m n) of
           Just p -> p
           Nothing -> return ()
--This clause is unchanged from GenerateC:
introduceSpec (A.Specification _ n (A.Is _ am t v))
    =  do let rhs = abbrevVariable am t v
          genDecl am t n
          tell [" = "]
          rhs
          tell [";\n"]
--Clause only changed to use Blitz++ rather than C arrays:
introduceSpec (A.Specification _ n (A.IsExpr _ am t e))
    =  do let rhs = abbrevExpression am t e
          case (am, t, e) of
            (A.ValAbbrev, A.Array _ ts, A.Literal _ (A.Array dims _)  _) ->
              -- For "VAL []T a IS [vs]:", we have to use [] rather than * in the
              -- declaration, since you can't say "int *foo = {vs};" in C.
              do tmp <- makeNonce "array_literal"
                 tell ["const "]
                 genType ts
                 tell [" ",tmp, " [] = "]
                 rhs
                 tell [" ; "]
                 tell ["const tockArrayView< const "]
                 genType ts
                 tell [" , ",show (length dims)," /**/>/**/ "]
                 genName n
                 tell ["(("]
                 genType ts 
                 tell [" *)",tmp,",tockDims("]
                 genDims dims
                 tell ["));\n"]
            (A.ValAbbrev, A.Record _, A.Literal _ _ _) ->
              -- Record literals are even trickier, because there's no way of
              -- directly writing a struct literal in C that you can use -> on.
              do tmp <- makeNonce "record_literal"
                 tell ["const "]
                 genType t
                 tell [" ", tmp, " = "]
                 rhs
                 tell [";\n"]
                 genDecl am t n
                 tell [" = &", tmp, ";\n"]
            _ ->
              do genDecl am t n
                 tell [" = "]
                 rhs
                 tell [";\n"]

--We must create the channel array then fill it:
introduceSpec (A.Specification _ n (A.IsChannelArray _ t cs))
    =  do genDeclaration t n
          sequence_ $ map genChanArrayElemInit (zip [0 .. ((length cs) - 1)] cs)
          where
            genChanArrayElemInit (index,var)
              = do genName n
                   tell ["[",show index,"].access() = "] --Use the .access() function to cast a 0-dimension array into a T& for access
                   genVariable var
                   tell [";"]
--This clause is unchanged from GenerateC:
introduceSpec (A.Specification _ _ (A.DataType _ _)) = return ()
--This clause was simplified, because the array handling could be removed:
introduceSpec (A.Specification _ n (A.RecordType _ b fs))
    =  do tell ["typedef struct {\n"]
          sequence_ [genDeclaration t n
                     | (n, t) <- fs]
          tell ["} "]
          when b $ tell ["occam_struct_packed "]
          genName n
          tell [";\n"]
--We do sequential protocols by introducing a new tuple:
introduceSpec (A.Specification _ n (A.Protocol _ typeList))
    =  do createChainedType "boost::tuple" (genProtocolName n) $ map genType typeList          
--We do variant protocols by introducing a new variant:
introduceSpec (A.Specification _ n (A.ProtocolCase _ []))
    =  do tell ["typedef class {} "] 
          genName n
          tell [";"]
introduceSpec (A.Specification _ n (A.ProtocolCase _ caseList))
    =  do sequence_ [tell ["class "] >> genProtocolTagName n tag >> tell [" {}; "] | (tag , _) <- caseList]    
          cgmap (typedef_genCaseType n) caseList          
          createChainedType "boost::variant" (genProtocolName n) $ map ((genTupleProtocolTagName n) . fst) caseList
          where 
            typedef_genCaseType :: A.Name -> (A.Name, [A.Type]) -> CGen()
            typedef_genCaseType n (tag, typeList) 
              =  createChainedType "boost::tuple" (genTupleProtocolTagName n tag) ((genProtocolTagName n tag) : (map genType typeList))
          
--Clause changed to handle array retyping
introduceSpec (A.Specification _ n (A.Retypes m am t v))
    =  do origT <- typeOfVariable v
          let rhs = abbrevVariable A.Abbrev origT v
          genDecl am t n
          tell [" = "]
          case t of 
            (A.Array dims _) ->
              --Arrays need to be handled differently because we need to feed the sizes in, not just perform a straight cast
              do genDeclType am t
                 tell ["("]
                 rhs
                 tell [",tockDims("]
                 genDims dims
                 tell ["));"]            
            _ ->      
              -- For scalar types that are VAL abbreviations (e.g. VAL INT64),
              -- we need to dereference the pointer that abbrevVariable gives us.
              do let deref = case (am, t) of
                               (_, A.Array _ _) -> False
                               (_, A.Chan _) -> False
                               (A.ValAbbrev, _) -> True
                               _ -> False
                 when deref $ tell ["*"]
                 tell ["("]
                 genDeclType am t
                 when deref $ tell [" *"]
                 tell [") ("]
                 rhs                 
                 case origT of 
                     --We must be retyping from an array, but not to an array (so to a primitive type or something):
                   (A.Array _ _) -> tell [".data()"]
                   _ -> return ()
                 tell [");\n"]

--This clause is unchanged from GenerateC:
introduceSpec n = missing $ "introduceSpec " ++ show n

--The only change from GenerateC are the two clauses relating to size:
genExpression :: A.Expression -> CGen ()
genExpression (A.Monadic m op e) = genMonadic m op e
genExpression (A.Dyadic m op e f) = genDyadic m op e f
genExpression (A.MostPos m t) = genTypeSymbol "mostpos" t
genExpression (A.MostNeg m t) = genTypeSymbol "mostneg" t
genExpression (A.SizeExpr m e)
    =  do genExpression e
          tell [" .extent(0) "]
genExpression (A.SizeVariable m v)
    =  do genVariable v
          tell [" .extent(0)"]
genExpression (A.Conversion m cm t e) = genConversion m cm t e
genExpression (A.ExprVariable m v) = genVariable v
genExpression (A.Literal _ _ lr) = genLiteral lr
genExpression (A.True m) = tell ["true"]
genExpression (A.False m) = tell ["false"]
--genExpression (A.FunctionCall m n es)
genExpression (A.IntrinsicFunctionCall m s es) = genIntrinsicFunction m s es
--genExpression (A.SubscriptedExpr m s e)
--genExpression (A.BytesInExpr m e)
genExpression (A.BytesInType m t) = genBytesIn t Nothing
--genExpression (A.OffsetOf m t n)
genExpression t = missing $ "genExpression " ++ show t
                                   
--}}}


--{{{  types
-- | If a type maps to a simple C type, return Just that; else return Nothing.

--Changed from GenerateC to change the A.Timer type to use C++CSP time
--Also changed the bool type, because vector<bool> in C++ is odd, so we hide it from the compiler:
scalarType :: A.Type -> Maybe String
scalarType A.Bool = Just "tockBool"
scalarType A.Byte = Just "uint8_t"
scalarType A.Int = Just "int"
scalarType A.Int16 = Just "int16_t"
scalarType A.Int32 = Just "int32_t"
scalarType A.Int64 = Just "int64_t"
scalarType A.Real32 = Just "float"
scalarType A.Real64 = Just "double"
scalarType A.Timer = Just "csp::Time"
scalarType _ = Nothing

--Generates an array type, giving the Blitz++ array the correct dimensions
genArrayType :: Bool -> A.Type -> Int -> CGen ()
genArrayType const (A.Array dims t) rank
    =  genArrayType const t (rank + (max 1 (length dims)))
genArrayType const t rank
    =  do tell [" tockArrayView< "]
          when (const) (tell [" const "])
          genType t
          tell [" , ",show rank, " > /**/"]
    
--Changed from GenerateC to change the arrays and the channels
--Also changed to add counted arrays and user protocols
genType :: A.Type -> CGen ()
genType arr@(A.Array _ _)
    =  genArrayType False arr 0    
genType (A.Record n) = genName n
genType (A.UserProtocol n) = genProtocolName n
genType (A.Chan t) 
    = do tell ["csp::One2OneChannel < "]
         genType t 
         tell [" > * "]
genType (A.Counted countType valueType)
    = genType (A.Array [A.UnknownDimension] valueType)
genType (A.Any)
    = tell [" tockAny "]
-- Any -- not used
--genType (A.Port t) =
genType t
    = case scalarType t of
        Just s -> tell [s]
        Nothing -> missing $ "genType " ++ show t


--Changed from GenerateC to add a name function (to allow us to use the same function for doing function parameters as constructor parameters)
--and also changed to use infixComma
--To use for a constructor list, pass prefixUnderscore as the function, otherwise pass the identity function
genFormals :: (A.Name -> A.Name) -> [A.Formal] -> CGen ()
genFormals nameFunc list = infixComma (map (genFormal nameFunc) list)

--Changed as genFormals
genFormal :: (A.Name -> A.Name) -> A.Formal -> CGen ()
genFormal nameFunc (A.Formal am t n) = genDecl am t (nameFunc n)

--Helper function for prefixing an underscore (looks like fairly ugly Haskell - maybe there is an easier way?)
prefixUnderscore :: A.Name -> A.Name
prefixUnderscore n = A.Name {A.nameMeta = A.nameMeta n, A.nameType = A.nameType n, A.nameName = "_" ++ A.nameName n}


-- | Generate the right-hand side of an abbreviation of a variable.
--Changed from GenerateC because we no longer need the A.Name -> CGen() function returned that dealt with array sizes
--I also pass the type of the array through to genSlice
abbrevVariable :: A.AbbrevMode -> A.Type -> A.Variable -> CGen ()
abbrevVariable am (A.Array _ _) v@(A.SubscriptedVariable _ (A.Subscript _ _) _)
    = genArrayAbbrev v
abbrevVariable am ty@(A.Array ds _) v@(A.SubscriptedVariable _ (A.SubscriptFromFor _ start count) v')
    = genSlice v v' ty start count ds
abbrevVariable am ty@(A.Array ds _) v@(A.SubscriptedVariable m (A.SubscriptFrom _ start) v')
    = genSlice v v' ty start (A.Dyadic m A.Minus (A.SizeExpr m (A.ExprVariable m v')) start) ds
abbrevVariable am ty@(A.Array ds _) v@(A.SubscriptedVariable m (A.SubscriptFor _ count) v')
    = genSlice v v' ty (makeConstant m 0) count ds
abbrevVariable am (A.Array _ _) v
    = genVariable v
abbrevVariable am (A.Chan _) v
    = genVariable v
abbrevVariable am (A.Record _) v
    = genVariable v
abbrevVariable am t v
    = genVariableAM v am


--Use C++ array slices:
--TODO put index checking back:
genSlice :: A.Variable -> A.Variable -> A.Type -> A.Expression -> A.Expression -> [A.Dimension] -> CGen ()
genSlice _ v ty start count ds
       -- We need to disable the index check here because we might be taking
       -- element 0 of a 0-length array -- which is valid.
    = do  genVariableUnchecked v
          tell [".sliceFromFor("]        
          genExpression start
          tell [" , "]
          genExpression count
          tell [")"]          
         

--Removed the sizing and the & from GenerateC:
genArrayAbbrev :: A.Variable -> CGen ()
genArrayAbbrev = genVariable 


--Changed from GenerateC to use Blitz++ subscripting (round brackets with commas) rather than traditional C indexing
genArraySubscript :: Bool -> A.Variable -> [A.Expression] -> CGen ()
genArraySubscript checkValid v es
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
                        genExpression e
                        tell [", "]
                        genVariable v
                        tell [".extent(", show sub, "), "]
                        genMeta (findMeta e)
                        tell [")"]
                else genExpression e
--}}}

-- | Map an operation over every item of an occam array.
--Changed from GenerateC because it uses the array sizes of Blitz++
overArray :: Meta -> A.Variable -> (SubscripterFunction -> Maybe (CGen ())) -> CGen ()
overArray m var func
    =  do A.Array ds _ <- typeOfVariable var
          specs <- sequence [makeNonceVariable "i" m A.Int A.VariableName A.Original | _ <- ds]
          let indices = [A.Variable m n | A.Specification _ n _ <- specs]

          let arg = (\var -> foldl (\v s -> A.SubscriptedVariable m s v) var [A.Subscript m $ A.ExprVariable m i | i <- indices])
          case func arg of
            Just p ->
              do sequence_ [do tell ["for (int "]
                               genVariable i
                               tell [" = 0; "]
                               genVariable i
                               tell [" < "]
                               genVariable var
                               tell [".extent(", show v, "); "]
                               genVariable i
                               tell ["++) {\n"]
                            | (v, i) <- zip [0..] indices]
                 p
                 sequence_ [tell ["}\n"] | _ <- indices]
            Nothing -> return ()



-- | Generate an expression inside a record literal.
--
-- This is awkward: the sort of literal that this produces when there's a
-- variable in here cannot always be compiled at the top level of a C99 program
-- -- because in C99, an array subscript is not a constant, even if it's a
-- constant subscript of a constant array.  So we need to be sure that when we
-- use this at the top level, the thing we're unfolding only contains literals.
-- Yuck!

--Changed to remove array size:
genUnfoldedExpression :: A.Expression -> CGen ()
genUnfoldedExpression (A.Literal _ t lr)
    =  genLiteralRepr lr
genUnfoldedExpression (A.ExprVariable m var) = genUnfoldedVariable m var
genUnfoldedExpression e = genExpression e

--Changed to remove array size:
genUnfoldedVariable :: Meta -> A.Variable -> CGen ()
genUnfoldedVariable m var
    =  do t <- typeOfVariable var
          case t of
            A.Array ds _ ->
              do genLeftB
                 unfoldArray ds var
                 genRightB
            A.Record _ ->
              do genLeftB
                 fs <- recordFields m t
                 seqComma [genUnfoldedVariable m (A.SubscriptedVariable m (A.SubscriptField m n) var)
                           | (n, t) <- fs]
                 genRightB
            -- We can defeat the usage check here because we know it's safe; *we're*
            -- generating the subscripts.
            -- FIXME Is that actually true for something like [a[x]]?
            _ -> genVariable' False var
  where
    unfoldArray :: [A.Dimension] -> A.Variable -> CGen ()
    unfoldArray [] v = genUnfoldedVariable m v
    unfoldArray (A.Dimension n:ds) v
      = seqComma $ [unfoldArray ds (A.SubscriptedVariable m (A.Subscript m $ makeConstant m i) v)
                    | i <- [0..(n - 1)]]
    unfoldArray _ _ = dieP m "trying to unfold array with unknown dimension"


--{{{  if
--Changed to throw a nonce-exception class instead of the goto, because C++ doesn't allow gotos to cross class initialisations (such as arrays)

genIf :: Meta -> A.Structured -> CGen ()
genIf m s
    =  do ifExc <- makeNonce "if_exc"
          tell ["class ",ifExc, " {}; try {"]
          genIfBody ifExc s
          genStop m "no choice matched in IF process"
          tell ["} catch (",ifExc,") {}"]

genIfBody :: String -> A.Structured -> CGen ()
genIfBody ifExc s = genStructured s doC
  where
    doC (A.OnlyC m (A.Choice m' e p))
        = do tell ["if ("]
             genExpression e
             tell [") {\n"]
             genProcess p             
             tell ["throw ",ifExc, "(); }\n"]
--}}}


--Changed to make array VAL abbreviations have constant data:
genDeclType :: A.AbbrevMode -> A.Type -> CGen ()
genDeclType am t
    =  do case t of
            A.Array _ _ -> genArrayType (am == A.ValAbbrev) t 0
            _ ->
              do when (am == A.ValAbbrev) $ tell ["const "]
                 genType t
                 case t of
                   A.Chan _ -> return ()
                   A.Record _ -> tell [" *"]
                   _ -> when (am == A.Abbrev) $ tell [" *"]



{-

---------------------------------------------------------------------

All the code below this point has been taken verbatim from GenerateC:

---------------------------------------------------------------------

-}

--Taken verbatim from GenerateC
genProcess :: A.Process -> CGen ()
genProcess p = case p of
  A.Assign m vs es -> genAssign m vs es
  A.Input m c im -> genInput c im
  A.Output m c ois -> genOutput c ois
  A.OutputCase m c t ois -> genOutputCase c t ois
  A.Skip m -> tell ["/* skip */\n"]
  A.Stop m -> genStop m "STOP process"
  A.Main m -> tell ["/* main */\n"]
  A.Seq _ s -> genSeqBody s
  A.If m s -> genIf m s
  A.Case m e s -> genCase m e s
  A.While m e p -> genWhile e p
  A.Par m pm s -> genPar pm s
  -- PROCESSOR does nothing special.
  A.Processor m e p -> genProcess p
  A.Alt m b s -> genAlt b s
  A.ProcCall m n as -> genProcCall n as
  A.IntrinsicProcCall m s as -> genIntrinsicProc m s as

--Taken verbatim from GenerateC
genAssign :: Meta -> [A.Variable] -> A.ExpressionList -> CGen ()
genAssign m [v] el
    = case el of
        A.FunctionCallList _ _ _ -> missing "function call"
        A.ExpressionList _ [e] ->
          do t <- typeOfVariable v
             doAssign t v e
  where
    doAssign :: A.Type -> A.Variable -> A.Expression -> CGen ()
    doAssign t@(A.Array _ subT) toV (A.ExprVariable m fromV)
        = overArray m fromV (\sub -> Just $ doAssign subT (sub toV) (A.ExprVariable m (sub fromV)))
    doAssign rt@(A.Record _) toV (A.ExprVariable m fromV)
        =  do fs <- recordFields m rt
              sequence_ [let subV v = A.SubscriptedVariable m (A.SubscriptField m n) v
                           in doAssign t (subV toV) (A.ExprVariable m $ subV fromV)
                         | (n, t) <- fs]
    doAssign t v e
        = case scalarType t of
            Just _ ->
              do genVariable v
                 tell [" = "]
                 genExpression e
                 tell [";\n"]
            Nothing -> missing $ "assignment of type " ++ show t


--Taken verbatim from GenerateC
genSeqBody :: A.Structured -> CGen ()
genSeqBody s = genStructured s doP
  where
    doP (A.OnlyP _ p) = genProcess p

--{{{  while
--Taken verbatim from GenerateC
genWhile :: A.Expression -> A.Process -> CGen ()
genWhile e p
    =  do tell ["while ("]
          genExpression e
          tell [") {\n"]
          genProcess p
          tell ["}\n"]
--}}}

--Taken verbatim from GenerateC
genStructured :: A.Structured -> (A.Structured -> CGen ()) -> CGen ()
genStructured (A.Rep _ rep s) def = genReplicator rep (genStructured s def)
genStructured (A.Spec _ spec s) def = genSpec spec (genStructured s def)
genStructured (A.ProcThen _ p s) def = genProcess p >> genStructured s def
genStructured (A.Several _ ss) def = sequence_ [genStructured s def | s <- ss]
genStructured s def = def s


--{{{  replicators
--All taken verbatim from GenerateC

genReplicator :: A.Replicator -> CGen () -> CGen ()
genReplicator rep body
    =  do tell ["for ("]
          genReplicatorLoop rep
          tell [") {\n"]
          body
          tell ["}\n"]

genReplicatorLoop :: A.Replicator -> CGen ()
genReplicatorLoop (A.For m index base count)
    = if isZero base
        then genSimpleReplicatorLoop index count
        else genGeneralReplicatorLoop index base count

genSimpleReplicatorLoop :: A.Name -> A.Expression -> CGen ()
genSimpleReplicatorLoop index count
    =  do tell ["int "]
          genName index
          tell [" = 0; "]
          genName index
          tell [" < "]
          genExpression count
          tell ["; "]
          genName index
          tell ["++"]

genGeneralReplicatorLoop :: A.Name -> A.Expression -> A.Expression -> CGen ()
genGeneralReplicatorLoop index base count
    =  do counter <- makeNonce "replicator_count"
          tell ["int ", counter, " = "]
          genExpression count
          tell [", "]
          genName index
          tell [" = "]
          genExpression base
          tell ["; ", counter, " > 0; ", counter, "--, "]
          genName index
          tell ["++"]

genReplicatorSize :: A.Replicator -> CGen ()
genReplicatorSize rep = genExpression (sizeOfReplicator rep)
--}}}

--Taken verbatim from GenerateC
genSpec :: A.Specification -> CGen () -> CGen ()
genSpec spec body
    =  do introduceSpec spec
          body
          removeSpec spec

--Taken verbatim from GenerateC
genIntrinsicFunction :: Meta -> String -> [A.Expression] -> CGen ()
genIntrinsicFunction m s es
    =  do tell ["occam_", s, " ("]
          sequence [genExpression e >> genComma | e <- es]
          genMeta m
          tell [")"]

--{{{  operators
--All taken verbatim from GenerateC

genSimpleMonadic :: String -> A.Expression -> CGen ()
genSimpleMonadic s e
    =  do tell ["(", s]
          genExpression e
          tell [")"]

genMonadic :: Meta -> A.MonadicOp -> A.Expression -> CGen ()
genMonadic _ A.MonadicSubtr e = genSimpleMonadic "-" e
genMonadic _ A.MonadicBitNot e = genSimpleMonadic "~" e
genMonadic _ A.MonadicNot e = genSimpleMonadic "!" e

genSimpleDyadic :: String -> A.Expression -> A.Expression -> CGen ()
genSimpleDyadic s e f
    =  do tell ["("]
          genExpression e
          tell [" ", s, " "]
          genExpression f
          tell [")"]

genFuncDyadic :: Meta -> String -> A.Expression -> A.Expression -> CGen ()
genFuncDyadic m s e f
    =  do t <- typeOfExpression e
          genTypeSymbol s t
          tell [" ("]
          genExpression e
          tell [", "]
          genExpression f
          tell [", "]
          genMeta m
          tell [")"]

genDyadic :: Meta -> A.DyadicOp -> A.Expression -> A.Expression -> CGen ()
genDyadic m A.Add e f = genFuncDyadic m "add" e f
genDyadic m A.Subtr e f = genFuncDyadic m "subtr" e f
genDyadic m A.Mul e f = genFuncDyadic m "mul" e f
genDyadic m A.Div e f = genFuncDyadic m "div" e f
genDyadic m A.Rem e f = genFuncDyadic m "rem" e f
genDyadic _ A.Plus e f = genSimpleDyadic "+" e f
genDyadic _ A.Minus e f = genSimpleDyadic "-" e f
genDyadic _ A.Times e f = genSimpleDyadic "*" e f
genDyadic _ A.LeftShift e f = genSimpleDyadic "<<" e f
genDyadic _ A.RightShift e f = genSimpleDyadic ">>" e f
genDyadic _ A.BitAnd e f = genSimpleDyadic "&" e f
genDyadic _ A.BitOr e f = genSimpleDyadic "|" e f
genDyadic _ A.BitXor e f = genSimpleDyadic "^" e f
genDyadic _ A.And e f = genSimpleDyadic "&&" e f
genDyadic _ A.Or e f = genSimpleDyadic "||" e f
genDyadic _ A.Eq e f = genSimpleDyadic "==" e f
genDyadic _ A.NotEq e f = genSimpleDyadic "!=" e f
genDyadic _ A.Less e f = genSimpleDyadic "<" e f
genDyadic _ A.More e f = genSimpleDyadic ">" e f
genDyadic _ A.LessEq e f = genSimpleDyadic "<=" e f
genDyadic _ A.MoreEq e f = genSimpleDyadic ">=" e f
   

genConversion :: Meta -> A.ConversionMode -> A.Type -> A.Expression -> CGen ()
genConversion m A.DefaultConversion toT e
    =  do fromT <- typeOfExpression e
          genCheckedConversion m fromT toT (genExpression e)
genConversion m cm toT e
    =  do fromT <- typeOfExpression e
          case (isSafeConversion fromT toT, isRealType fromT, isRealType toT) of
            (True, _, _) ->
              -- A safe conversion -- no need for a check.
              genCheckedConversion m fromT toT (genExpression e)
            (_, True, True) ->
              -- Real to real.
              do genConversionSymbol fromT toT cm
                 tell [" ("]
                 genExpression e
                 tell [", "]
                 genMeta m
                 tell [")"]
            (_, True, False) ->
              -- Real to integer -- do real -> int64_t -> int.
              do let exp = do genConversionSymbol fromT A.Int64 cm
                              tell [" ("]
                              genExpression e
                              tell [", "]
                              genMeta m
                              tell [")"]
                 genCheckedConversion m A.Int64 toT exp
            (_, False, True) ->
              -- Integer to real -- do int -> int64_t -> real.
              do genConversionSymbol A.Int64 toT cm
                 tell [" ("]
                 genCheckedConversion m fromT A.Int64 (genExpression e)
                 tell [", "]
                 genMeta m
                 tell [")"]
            _ -> missing $ "genConversion " ++ show cm

genConversionSymbol :: A.Type -> A.Type -> A.ConversionMode -> CGen ()
genConversionSymbol fromT toT cm
    =  do tell ["occam_convert_"]
          genType fromT
          tell ["_"]
          genType toT
          tell ["_"]
          case cm of
            A.Round -> tell ["round"]
            A.Trunc -> tell ["trunc"]

genCheckedConversion :: Meta -> A.Type -> A.Type -> CGen () -> CGen ()
genCheckedConversion m fromT toT exp
    =  do tell ["(("]
          genType toT
          tell [") "]
          if isSafeConversion fromT toT
            then exp
            else do genTypeSymbol "range_check" fromT
                    tell [" ("]
                    genTypeSymbol "mostneg" toT
                    tell [", "]
                    genTypeSymbol "mostpos" toT
                    tell [", "]
                    exp
                    tell [", "]
                    genMeta m
                    tell [")"]
          tell [")"]
--}}}


--{{{  declarations
--All taken verbatim from GenerateC

genDecl :: A.AbbrevMode -> A.Type -> A.Name -> CGen ()
genDecl am t n
    =  do genDeclType am t
          tell [" "]
          genName n
--}}}

--{{{  case
--All taken verbatim from GenerateC
genCase :: Meta -> A.Expression -> A.Structured -> CGen ()
genCase m e s
    =  do tell ["switch ("]
          genExpression e
          tell [") {\n"]
          seenDefault <- genCaseBody (return ()) s
          when (not seenDefault) $
            do tell ["default:\n"]
               genStop m "no option matched in CASE process"
          tell ["}\n"]

-- FIXME -- can this be made common with genInputCaseBody above?
genCaseBody :: CGen () -> A.Structured -> CGen Bool
genCaseBody coll (A.Spec _ spec s)
    = genCaseBody (genSpec spec coll) s
genCaseBody coll (A.OnlyO _ (A.Option _ es p))
    =  do sequence_ [tell ["case "] >> genExpression e >> tell [":\n"] | e <- es]
          tell ["{\n"]
          coll
          genProcess p
          tell ["break;\n"]
          tell ["}\n"]
          return False
genCaseBody coll (A.OnlyO _ (A.Else _ p))
    =  do tell ["default:\n"]
          tell ["{\n"]
          coll
          genProcess p
          tell ["}\n"]
          return True
genCaseBody coll (A.Several _ ss)
    =  do seens <- mapM (genCaseBody coll) ss
          return $ or seens
--}}}


-- | Generate C code for a variable.
--Taken verbatim from GenerateC
genVariable :: A.Variable -> CGen ()
genVariable = genVariable' True

-- | Generate C code for a variable without doing any range checks.
--Taken verbatim from GenerateC
genVariableUnchecked :: A.Variable -> CGen ()
genVariableUnchecked = genVariable' False

--Taken verbatim from GenerateC
genVariable' :: Bool -> A.Variable -> CGen ()
genVariable' checkValid v
    =  do am <- accessAbbrevMode v
          t <- typeOfVariable v
          let isSub = case v of
                        A.Variable _ _ -> False
                        A.SubscriptedVariable _ _ _ -> True

          let prefix = case (am, t) of
                         (_, A.Array _ _) -> ""
                         (A.Original, A.Chan _) -> if isSub then "" else "&"
                         (A.Abbrev, A.Chan _) -> ""
                         (A.Original, A.Record _) -> "&"
                         (A.Abbrev, A.Record _) -> ""
                         (A.Abbrev, _) -> "*"
                         _ -> ""

          when (prefix /= "") $ tell ["(", prefix]
          inner v
          when (prefix /= "") $ tell [")"]
  where
    -- | Find the effective abbreviation mode for the variable we're looking at.
    -- This differs from abbrevModeOfVariable in that it will return Original
    -- for array and record elements (because when we're generating C, we can
    -- treat c->x as if it's just x).
    accessAbbrevMode :: A.Variable -> CGen A.AbbrevMode
    accessAbbrevMode (A.Variable _ n) = abbrevModeOfName n
    accessAbbrevMode (A.SubscriptedVariable _ sub v)
        =  do am <- accessAbbrevMode v
              return $ case (am, sub) of
                         (_, A.Subscript _ _) -> A.Original
                         (_, A.SubscriptField _ _) -> A.Original
                         _ -> am

    inner :: A.Variable -> CGen ()
    inner (A.Variable _ n) = genName n
    inner sv@(A.SubscriptedVariable _ (A.Subscript _ _) _)
        =  do let (es, v) = collectSubs sv
              genVariable v
              genArraySubscript checkValid v es
              t <- typeOfVariable v
              --To index an actual element of an array we must use the .access() function
              --Only needed when we have applied enough subscripts to get out an element:
              case t of A.Array dims _ -> when ((length dims) == (length es)) (tell [" .access() "])
    inner (A.SubscriptedVariable _ (A.SubscriptField m n) v)
        =  do genVariable v
              tell ["->"]
              genName n
    inner (A.SubscriptedVariable m (A.SubscriptFromFor m' start _) v)
        = inner (A.SubscriptedVariable m (A.Subscript m' start) v)
    inner (A.SubscriptedVariable m (A.SubscriptFrom m' start) v)
        = inner (A.SubscriptedVariable m (A.Subscript m' start) v)
    inner (A.SubscriptedVariable m (A.SubscriptFor m' _) v)
        = inner (A.SubscriptedVariable m (A.Subscript m' (makeConstant m' 0)) v)

    -- | Collect all the plain subscripts on a variable, so we can combine them.
    collectSubs :: A.Variable -> ([A.Expression], A.Variable)
    collectSubs (A.SubscriptedVariable _ (A.Subscript _ e) v)
        = (es' ++ [e], v')
      where
        (es', v') = collectSubs v
    collectSubs v = ([], v)

--Taken verbatim from GenerateC due to export annoyances:
data InputType = ITTimerRead | ITTimerAfter | ITOther

-- | Given an input mode, figure out what sort of input it's actually doing.
--Taken verbatim from GenerateC due to export annoyances:
inputType :: A.Variable -> A.InputMode -> CGen InputType
inputType c im
    =  do t <- typeOfVariable c
          return $ case t of
                     A.Timer ->
                       case im of
                         A.InputSimple _ _ -> ITTimerRead
                         A.InputAfter _ _ -> ITTimerAfter
                     _ -> ITOther


--Taken verbatim from GenerateC
genVariableAM :: A.Variable -> A.AbbrevMode -> CGen ()
genVariableAM v am
    =  do when (am == A.Abbrev) $ tell ["&"]
          genVariable v

--{{{  literals
--All taken verbatim from GenerateC
genLiteral :: A.LiteralRepr -> CGen ()
genLiteral lr
    = if isStringLiteral lr
        then do tell ["\""]
                let A.ArrayLiteral _ aes = lr
                sequence_ [genByteLiteral s
                           | A.ArrayElemExpr (A.Literal _ _ (A.ByteLiteral _ s)) <- aes]
                tell ["\""]
        else genLiteralRepr lr

genLiteralRepr :: A.LiteralRepr -> CGen ()
genLiteralRepr (A.RealLiteral m s) = tell [s]
genLiteralRepr (A.IntLiteral m s) = genDecimal s
genLiteralRepr (A.HexLiteral m s) = tell ["0x", s]
genLiteralRepr (A.ByteLiteral m s) = tell ["'"] >> genByteLiteral s >> tell ["'"]
genLiteralRepr (A.ArrayLiteral m aes)
    =  do genLeftB
          genArrayLiteralElems aes
          genRightB
genLiteralRepr (A.RecordLiteral _ es)
    =  do genLeftB
          seqComma $ map genUnfoldedExpression es
          genRightB

genArrayLiteralElems :: [A.ArrayElem] -> CGen ()
genArrayLiteralElems aes
    = seqComma $ map genElem aes
  where
    genElem :: A.ArrayElem -> CGen ()
    genElem (A.ArrayElemArray aes) = genArrayLiteralElems aes
    genElem (A.ArrayElemExpr e) = genUnfoldedExpression e



--}}}

--Taken verbatim from GenerateC:
withIf :: A.Expression -> CGen () -> CGen ()
withIf cond body
    =  do tell ["if ("]
          genExpression cond
          tell [") {\n"]
          body
          tell ["}\n"]
          
--Taken verbatim from GenerateC
genAltProcesses :: String -> String -> String -> A.Structured -> CGen ()
genAltProcesses id fired label s = genStructured s doA
  where
    doA (A.OnlyA _ alt)
        = case alt of
            A.Alternative _ c im p -> doIn c im p
            A.AlternativeCond _ e c im p -> withIf e $ doIn c im p
            A.AlternativeSkip _ e p -> withIf e $ doCheck (genProcess p)

    doIn c im p
        = do t <- inputType c im
             case t of
               ITTimerRead -> missing "timer read in ALT"
               ITTimerAfter -> doCheck (genProcess p)
               ITOther -> doCheck (genInput c im >> genProcess p)

    doCheck body
        = do tell ["if (", id, "++ == ", fired, ") {\n"]
             body
             tell ["goto ", label, ";\n"]
             tell ["}\n"]

          
