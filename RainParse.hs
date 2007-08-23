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

module RainParse where

import qualified Text.ParserCombinators.Parsec.Token as P
import qualified LexRain as L




--Chuck a whole load from Parse:
import Control.Monad (liftM, when)
import Control.Monad.Error (runErrorT)
import Control.Monad.State (MonadState, StateT, execStateT, liftIO, modify, get, put)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import qualified IO
import Numeric (readHex)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos (newPos)
import Text.Regex

import qualified AST as A
import CompState
import Errors
import EvalConstants
import EvalLiterals
import Intrinsics
import Metadata
import Pass
import Types
import Utils



type RainState = CompState
type RainParser = GenParser L.Token RainState

--{{{ Symbols
sLeftQ = reserved "["
sRightQ = reserved "]"
sLeftR = reserved "("
sRightR = reserved ")"
sLeftC = reserved "{"
sRightC = reserved "}"
sSemiColon = reserved ";"
sColon = reserved ":"
sComma = reserved ","
sIn = reserved "?"
sOut = reserved "!"
--}}}

--{{{ Keywords

sPar = reserved "par"
sSeq = reserved "seq"
sAlt = reserved "alt"
sSeqeach = reserved "seqeach"
sPareach = reserved "pareach"
sChannel = reserved "channel"
sOne2One = reserved "one2one"
sIf = reserved "if"
sElse = reserved "else"
sWhile = reserved "while"
sProcess = reserved "process"
sRun = reserved "run"
--}}}

--{{{Operators

dyadicArithOp :: RainParser (Meta,A.DyadicOp)
dyadicArithOp
  = do {m <- reserved "+" ; return (m,A.Plus) }
    <|> do {m <- reserved "-" ; return (m,A.Minus) }
    <|> do {m <- reserved "*" ; return (m,A.Times) }
    <|> do {m <- reserved "/" ; return (m,A.Div) }

dyadicCompOp :: RainParser (Meta,A.DyadicOp)
dyadicCompOp
  = do {m <- reserved "<" ; return (m,A.Less) }
    <|> do {m <- reserved ">" ; return (m,A.More) }
    <|> do {m <- reserved "<=" ; return (m,A.LessEq) }
    <|> do {m <- reserved ">=" ; return (m,A.MoreEq) }
    <|> do {m <- reserved "==" ; return (m,A.Eq) }

monadicArithOp :: RainParser (Meta,A.MonadicOp)
monadicArithOp
  = do {m <- reserved "-" ; return (m,A.MonadicSubtr) }



--}}}

metaToPos :: Meta -> SourcePos
metaToPos m = newPos (fromMaybe "" $ metaFile m) (metaLine m) (metaColumn m)

getToken :: (L.TokenType -> Maybe x) -> RainParser (Meta, x)
getToken test = token (show) (metaToPos . fst) (wrap test)
  where
    wrap :: (L.TokenType -> Maybe x) -> (Meta,L.TokenType) -> Maybe (Meta,x)
    wrap f (m,t) = case f t of
      Nothing -> Nothing
      Just t' -> Just (m,t')

identifier :: RainParser (Meta, String)
identifier = getToken testToken
  where
    testToken (L.TokIdentifier id) = Just id
    testToken _ = Nothing

reserved :: String -> RainParser Meta
reserved word 
  = (liftM fst) (getToken testToken)
    <?> ("reserved word: " ++ word)
      where
        testToken (L.TokReserved r) = if r == word then Just r else Nothing
        testToken _ = Nothing


name :: RainParser A.Name
name 
    =   do (m,s) <- identifier
           return $ A.Name m (A.VariableName) s --A.VariableName is a placeholder until a later pass
    <?> "name"


dataType :: RainParser A.Type
dataType 
  = do {reserved "bool" ; return A.Bool}
    <|> do {reserved "int" ; return A.Int}
    <|> do {reserved "uint8" ; return A.Byte}
    <|> do {reserved "uint16" ; return A.UInt16}
    <|> do {reserved "uint32" ; return A.UInt32}
    <|> do {reserved "uint64" ; return A.UInt64}
    <|> do {reserved "sint8" ; return A.Int8}
    <|> do {reserved "sint16" ; return A.Int16}
    <|> do {reserved "sint32" ; return A.Int32}
    <|> do {reserved "sint64" ; return A.Int64}    
    <|> do {sChannel ; inner <- dataType ; return $ A.Chan A.DirUnknown (A.ChanAttributes {A.caWritingShared = False, A.caReadingShared = False}) inner}
    <|> do {sIn ; inner <- dataType ; return $ A.Chan A.DirInput (A.ChanAttributes {A.caWritingShared = False, A.caReadingShared = False}) inner}
    <|> do {sOut ; inner <- dataType ; return $ A.Chan A.DirOutput (A.ChanAttributes {A.caWritingShared = False, A.caReadingShared = False}) inner}
    <|> do {(m,n) <- identifier ; return $ A.UserDataType A.Name {A.nameMeta = m, A.nameName = n, A.nameType = A.DataTypeName}}
    <?> "data type"

variableId :: RainParser A.Variable
variableId = do {v <- name ; return $ A.Variable (findMeta v) v}
             <?> "variable name"

stringLiteral :: RainParser (A.LiteralRepr, A.Dimension)
stringLiteral
    =  do (m,str) <- getToken testToken
          let processed = replaceEscapes str
          let aes = [A.ArrayElemExpr $ A.Literal m A.Byte $ A.ByteLiteral m [c] | c <- processed]
          return (A.ArrayLiteral m aes, A.Dimension $ length processed)
    <?> "string literal"
  where
    testToken (L.TokStringLiteral str) = Just str
    testToken _ = Nothing
    replaceEscapes :: String -> String
    replaceEscapes [] = []
    replaceEscapes ('\\':(c:cs)) = if c == 'n' then ('\n':replaceEscapes cs) else (c:replaceEscapes cs)
    replaceEscapes (c:cs) = (c:replaceEscapes cs)

literalCharacter :: RainParser A.LiteralRepr
literalCharacter
    =   do (m,c) <- getToken testToken
           return $ A.ByteLiteral m c
  where
    testToken (L.TokCharLiteral c) = Just c
    testToken _ = Nothing
           
integer :: RainParser A.LiteralRepr
integer
    =  do (m,d) <- getToken testToken
          return $ A.IntLiteral m d
  where
    testToken (L.TokDecimalLiteral d) = Just d
    testToken _ = Nothing

literal :: RainParser A.Expression
literal = do {(lr, dim) <- stringLiteral ; return $ A.Literal (findMeta lr) (A.Array [dim] A.Byte) lr }
          <|> do {i <- integer ; return $ A.Literal (findMeta i) A.Int i}
          <|> do {m <- reserved "true" ; return $ A.True m}
          <|> do {m <- reserved "false" ; return $ A.False m}
          <?> "literal"

expression :: RainParser A.Expression
expression
  = try compExpression
    <|> try castExpression
    <|> try subExpression
    <?> "expression"
  where
    castExpression :: RainParser A.Expression
    castExpression = do {ty <- dataType ; m <- sColon ; e <- expression ; return $ A.Conversion m A.DefaultConversion ty e}

    compExpression :: RainParser A.Expression
    compExpression = do {lhs <- subExpression ; (m,op) <- dyadicCompOp ; rhs <- subExpression ; return $ A.Dyadic m op lhs rhs }

    subExpression :: RainParser A.Expression
    subExpression
      = do se <- subExpr'
           further <- many (do {(m, op) <- dyadicArithOp ; exp <- subExpr' ; return (m,op,exp)})
           --further :: [(Meta,A.DyadicOp,A.Expression)]
           return $ foldl foldOps se further

    foldOps :: A.Expression -> (Meta,A.DyadicOp,A.Expression) -> A.Expression
    foldOps lhs (m,op,rhs) = A.Dyadic m op lhs rhs

    subExpr' :: RainParser A.Expression
    subExpr' = do {id <- variableId ; return $ A.ExprVariable (findMeta id) id}
               <|> literal
               <|> do {(m,op) <- monadicArithOp ; rhs <- subExpr' ; return $ A.Monadic m op rhs}
               <|> do {sLeftR ; e <- expression ; sRightR ; return e}

innerBlock :: RainParser A.Structured
innerBlock = do {m <- sLeftC ; lines <- linesToEnd ; return $ A.Several m lines}
  where
    wrapProc :: A.Process -> A.Structured
    wrapProc x = A.OnlyP (findMeta x) x
    linesToEnd :: RainParser [A.Structured]
    linesToEnd = do {(m,decl) <- declaration ; rest <- linesToEnd ; return [decl $ A.Several m rest]}
                 <|> do {st <- statement ; rest <- linesToEnd ; return $ (wrapProc st) : rest}
                 <|> do {sRightC ; return []}
                 <?> "statement, declaration, or end of block"

block :: RainParser A.Process
block = do { optionalSeq ; b <- innerBlock ; return $ A.Seq (findMeta b) b}
        <|> do { m <- sPar ; b <- innerBlock ; return $ A.Par m A.PlainPar b}

optionalSeq :: RainParser ()
optionalSeq = option () (sSeq >> return ())

assignOp :: RainParser (Meta, Maybe A.DyadicOp)
--consume an optional operator, then an equals sign (so we can handle = += /= etc)  This should not handle !=, nor crazy things like ===, <== (nor <=)
assignOp
  = do {m <- reserved "+=" ; return (m,Just A.Plus)}
    <|> do {m <- reserved "-=" ; return (m,Just A.Minus)}
    <|> do {m <- reserved "=" ; return (m,Nothing)}	
    --TODO the rest

lvalue :: RainParser A.Variable
--For now, only handle plain variables:
lvalue = variableId

each :: RainParser A.Process
each = do { m <- sPareach ; sLeftR ; n <- name ; sColon ; exp <- expression ; sRightR ; st <- statement ; 
             return $ A.Par m A.PlainPar $ A.Rep m (A.ForEach m n exp) $ A.OnlyP m st }
       <|> do { m <- sSeqeach ; sLeftR ; n <- name ; sColon ; exp <- expression ; sRightR ; st <- statement ; 
             return $ A.Seq m $ A.Rep m (A.ForEach m n exp) $ A.OnlyP m st }

comm :: RainParser A.Process
comm = do { lv <- lvalue ; 
              do {sOut ; exp <- expression ; sSemiColon ; return $ A.Output (findMeta lv) lv [A.OutExpression (findMeta exp) exp] }
              <|> do {sIn ; rv <- lvalue ; sSemiColon ; return $ A.Input (findMeta lv) lv $ A.InputSimple (findMeta rv) [A.InVariable (findMeta rv) rv] }
          }

tuple :: RainParser [A.Expression]
tuple = do { sLeftR ; items <- expression `sepBy` sComma ; sRightR ; return items }

runProcess :: RainParser A.Process
runProcess = do m <- sRun
                (mProcess,processName) <- identifier
                items <- tuple
                sSemiColon
                return $ A.ProcCall m A.Name {A.nameName = processName, A.nameMeta = mProcess, A.nameType = A.ProcName} (map convertItem items)
  where
    convertItem :: A.Expression -> A.Actual
    convertItem (A.ExprVariable _ v) = A.ActualVariable A.Original A.Any v
    convertItem e = A.ActualExpression A.Any e

statement :: RainParser A.Process
statement 
  = do { m <- sWhile ; sLeftR ; exp <- expression ; sRightR ; st <- statement ; return $ A.While m exp st}
    <|> do { m <- sIf ; sLeftR ; exp <- expression ; sRightR ; st <- statement ; 
             option (A.If m $ A.Several m [A.OnlyC m (A.Choice m exp st), A.OnlyC m (A.Choice m (A.True m) (A.Skip m))])
                    (do {sElse ; elSt <- statement ; return (A.If m $ A.Several m [A.OnlyC m (A.Choice m exp st), A.OnlyC m (A.Choice m (A.True m) elSt)])})
           }
    <|> block
    <|> each
    <|> runProcess
    <|> try comm
    <|> try (do { lv <- lvalue ; op <- assignOp ; exp <- expression ; sSemiColon ; 
             case op of 
               (m', Just dyOp) -> return (A.Assign m' [lv] (A.ExpressionList m' [(A.Dyadic m' dyOp (A.ExprVariable (findMeta lv) lv) exp)]))
               (m', Nothing) -> return (A.Assign m' [lv] (A.ExpressionList (findMeta exp) [exp]))
           })   
    <|> do { m <- sSemiColon ; return $ A.Skip m}
    <?> "statement"

formaliseTuple :: [(A.Name,A.Type)] -> [A.Formal]
formaliseTuple = map (\(n,t) -> A.Formal A.ValAbbrev t n)

tupleDef :: RainParser [(A.Name,A.Type)]
tupleDef = do {sLeftR ; tm <- sepBy tupleDefMember sComma ; sRightR ; return tm}
  where
    tupleDefMember :: RainParser (A.Name,A.Type)
    tupleDefMember = do {t <- dataType ; sColon ; n <- name ; return (n,t)}

declaration :: RainParser (Meta,A.Structured -> A.Structured)
declaration = try $ do {t <- dataType; sColon ; n <- name ; sSemiColon ; 
  return (findMeta t, A.Spec (findMeta t) $ A.Specification (findMeta t) n $ A.Declaration (findMeta t) t) }

terminator :: A.Structured
terminator = (A.OnlyP emptyMeta $ A.Main emptyMeta)

processDecl :: RainParser A.Structured
processDecl = do {m <- sProcess ; procName <- name ; params <- tupleDef ; body <- block ;
  return $ A.Spec m
    (A.Specification m procName (A.Proc m A.PlainSpec (formaliseTuple params) body))
  terminator}

topLevelDecl :: RainParser A.Structured
topLevelDecl = do decls <- many processDecl
                  eof
                  return $ A.Several emptyMeta decls

rainSourceFile :: RainParser (A.Process, CompState)
rainSourceFile
    =   do p <- topLevelDecl
           s <- getState
           return (A.Seq emptyMeta p, s)

-- | Load and parse a Rain source file.
parseRainProgram :: String -> PassM A.Process
parseRainProgram filename
    =  do source <- liftIO $ readFile filename
          lexOut <- liftIO $ L.runLexer filename source          
          case lexOut of
            Left merr -> dieIO $ "Parse error at: " ++ (show merr)
            Right toks ->
              do cs <- get
                 case runParser rainSourceFile cs filename toks of
                   Left err -> dieIO $ "Parse error: " ++ show err
                   Right (p, cs') ->
                     do put cs'
                        return p
