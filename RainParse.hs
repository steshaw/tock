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
import Text.ParserCombinators.Parsec.Language (emptyDef)
import Text.Regex

import qualified AST as A
import CompState
import Errors
import EvalConstants
import EvalLiterals
import Indentation
import Intrinsics
import Metadata
import Pass
import Types
import Utils



type RainState = CompState
type RainParser = GenParser Char CompState

rainStyle 
  = emptyDef
  { P.commentLine    = "#"
    , P.nestedComments = False
    , P.identStart     = letter <|> char '_'
    , P.identLetter    = alphaNum <|> char '_'
    , P.opStart        = oneOf ":+-*/>=<!"
    , P.opLetter       = oneOf "+-="
    , P.reservedOpNames= [
                          "+",
                          "-",
                          "*",
                          "/",
                          "==",
                          "<",
                          ">",
                          ">=",
                          "<=",
                          "!=",
                          "-",
                          ":"
                         ]
    , P.reservedNames  = [
                          "par",
                          "seq",
                          "alt",
                          "seqeach",
                          "pareach",
                          "channel",
                          "one2one",
                          "int",
                          "if",
                          "while",
                          "process",
                          "bool"
{-                          
                          "tuple",
                          "sleep",
                          "for",
                          "until",
                          "poison",
                          "return",
                          "function",
                          "typedef",
                          "sint8","sint16","sint32","sint64"
                          "uint8","uint16","uint32","uint64"
                          "shared",
                          "template",
                          "constant",
                          "namespace"
-}                          
                         ]
    , P.caseSensitive  = True
    }
    
lexer :: P.TokenParser RainState
lexer  = P.makeTokenParser rainStyle

whiteSpace = P.whiteSpace lexer
lexeme = P.lexeme lexer
symbol = P.symbol lexer
natural = P.natural lexer
parens = P.parens lexer
semi = P.semi lexer
identifier = P.identifier lexer
reserved = P.reserved lexer
reservedOp = P.reservedOp lexer

--{{{ Symbols
sLeftQ = try $ symbol "["
sRightQ = try $ symbol "]"
sLeftR = try $ symbol "("
sRightR = try $ symbol ")"
sLeftC = try $ symbol "{"
sRightC = try $ symbol "}"
sEquality = try $ symbol "=="
sSemiColon = try $ symbol ";"
sColon = try $ symbol ":"
sQuote = try $ symbol "\""
--}}}

--{{{ Keywords

sPar = reserved "par"
sSeq = reserved "seq"
sAlt = reserved "alt"
sSeqeach = reserved "seqeach"
sPareach = reserved "pareach"
sChannel = reserved "channel"
sOne2One = reserved "one2one"
sBool = reserved "bool"
sInt = reserved "int"
sIf = reserved "if"
sElse = reserved "else"
sWhile = reserved "while"
sProcess = reserved "process"
--}}}

--{{{Ideas nicked from GenerateC:
md :: RainParser Meta
md
  =  do pos <- getPosition
        return Meta {
                 metaFile = Just $ sourceName pos,
                 metaLine = sourceLine pos,
                 metaColumn = sourceColumn pos
               }

name :: RainParser A.Name
name 
    =   do m <- md
           s <- identifier
           return $ A.Name m (A.VariableName) s --A.VariableName is a placeholder until a later pass
    <?> "name"

--}}}

dataType :: RainParser A.Type
dataType 
  = do {sBool ; return A.Bool}
    <|> do {sInt ; return A.Int64}
    <|> do {sChannel ; inner <- dataType ; return $ A.Chan inner}
    <?> "data type"

variableId :: RainParser A.Variable
variableId = do {m <- md ; v <- name ; return $ A.Variable m v}
             <?> "variable name"

stringLiteral :: RainParser (A.LiteralRepr, A.Dimension)
stringLiteral
    =  do m <- md
          char '"'
          cs <- manyTill literalCharacter sQuote
          let aes = [A.ArrayElemExpr $ A.Literal m A.Byte c | c <- cs]
          return (A.ArrayLiteral m aes, A.Dimension $ length cs)
    <?> "string literal"

literalCharacter :: RainParser A.LiteralRepr
literalCharacter
    =   do m <- md
           c <- anyChar
           return $ A.ByteLiteral m [c]
           
digits :: RainParser String
digits
    =   many1 digit
    <?> "decimal digits"

integer :: RainParser A.LiteralRepr
integer
    =  do m <- md
          d <- lexeme digits
          return $ A.IntLiteral m d

literal :: RainParser A.Expression
literal = do {m <- md ; (lr, dim) <- stringLiteral ; return $ A.Literal m (A.Array [dim] A.Byte) lr }
          <|> do {m <- md ; i <- integer ; return $ A.Literal m A.Int i}
          <?> "literal"

expression :: RainParser A.Expression
expression
  = do {m <- md ; lhs <- subExpression ; 
           do {sEquality ; rhs <- expression ; return $ A.Dyadic m A.Eq lhs rhs}
           <|> do {return lhs}           
       }
       <?> "expression"

subExpression :: RainParser A.Expression
subExpression
  = do {m <- md ; id <- variableId ; return $ A.ExprVariable m id}
    <|> literal
    <?> "[sub-]expression"

block :: RainParser A.Structured
block = do {m <- md ; sLeftC ; procs <- (many statement) ; sts <- sequence (map wrapProc procs) ; sRightC ; return $ A.Several m sts}
  where
    wrapProc :: A.Process -> RainParser A.Structured
    wrapProc x = return (A.OnlyP emptyMeta x)

optionalSeq :: RainParser ()
optionalSeq = option () sSeq

assignOp :: RainParser (Meta, Maybe A.DyadicOp)
--consume an optional operator, then an equals sign (so we can handle = += /= etc)  This should not handle !=, nor crazy things like ===, <== (nor <=)
assignOp
  = do {m <- md; reservedOp "+=" ; return (m,Just A.Plus)}
    <|> do {m <- md; reservedOp "-=" ; return (m,Just A.Minus)}
    <|> do {m <- md; reservedOp "=" ; return (m,Nothing)}	
    --TODO the rest

lvalue :: RainParser A.Variable
--For now, only handle plain variables:
lvalue = variableId

statement :: RainParser A.Process
statement 
  = do { m <- md ; sWhile ; sLeftR ; exp <- expression ; sRightR ; st <- statement ; return $ A.While m exp st}
    <|> do { m <- md ; sIf ; sLeftR ; exp <- expression ; sRightR ; st <- statement ; 
             option (A.If m $ A.Several m [A.OnlyC m (A.Choice m exp st), A.OnlyC m (A.Choice m (A.True m) (A.Skip m))])
                    (do {sElse ; elSt <- statement ; return (A.If m $ A.Several m [A.OnlyC m (A.Choice m exp st), A.OnlyC m (A.Choice m (A.True m) elSt)])})
           }
    <|> do { m <- md ; optionalSeq ; b <- block ; return $ A.Seq m b}
    <|> do { m <- md ; sPar ; b <- block ; return $ A.Par m A.PlainPar b}
    <|> do { m <- md ; sPareach ; sLeftR ; n <- name ; sColon ; exp <- expression ; sRightR ; st <- statement ; 
             return $ A.Par m A.PlainPar $ A.Rep m (A.ForEach m n exp) $ A.OnlyP m st }
    <|> do { m <- md ; sSeqeach ; sLeftR ; n <- name ; sColon ; exp <- expression ; sRightR ; st <- statement ; 
             return $ A.Seq m $ A.Rep m (A.ForEach m n exp) $ A.OnlyP m st }             
    <|> do { m <- md ; lv <- lvalue ; op <- assignOp ; exp <- expression ; sSemiColon ; 
             case op of 
               (m', Just dyOp) -> return (A.Assign m' [lv] (A.ExpressionList m' [(A.Dyadic m' dyOp (A.ExprVariable m lv) exp)]))
               (m', Nothing) -> return (A.Assign m' [lv] (A.ExpressionList m [exp]))
           }    
    <|> do { m <- md ; sSemiColon ; return $ A.Skip m}
    <?> "statement"

topLevelDecl :: RainParser A.Structured
topLevelDecl = return $ A.Several emptyMeta [] --Dummy value, for now

rainSourceFile :: RainParser (A.Process, CompState)
rainSourceFile
    =   do whiteSpace
           --TODO change from stattement to declaration (once the latter is written):
           p <- statement
           s <- getState
           return (p, s)

-- | Parse a file with the given production.
-- This is copied from Parse.hs (because OccParser is about to be changed to not be the same as RainParser):
parseFile :: Monad m => String -> RainParser t -> CompState -> m t
parseFile file prod ps
    =  do let source = case Map.lookup file (csSourceFiles ps) of
                         Just s -> s
                         Nothing -> dieIO $ "Failed to preload file: " ++ show file
          let ps' = ps { csLoadedFiles = file : csLoadedFiles ps }
          case runParser prod ps' file source of
            Left err -> dieIO $ "Parse error: " ++ show err
            Right r -> return r

parseRainProgram :: String -> PassM A.Process
parseRainProgram file
    =  do ps <- get
          (p, ps') <- parseFile file rainSourceFile ps
          put ps'
          return p
