{ {-
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

-- | Lexically analyse occam code.
module LexOccam where

import Data.Generics
import System

import Metadata
import PrettyShow
}

%wrapper "posn"

$decimalDigit = [0-9]
$hexDigit = [0-9 a-f A-F]

@reserved = "[" | "]" | "(" | ")"
          | "::" | ":=" | ":" | "," | ";" | "&"
          | "?" | "!" | "="
          | "\" | "/\" | "\/"
          | "+" | "-" | "*" | "/"
          | "><" | "<<" | ">>" | "<>"
          | ">=" | "<="
          | "<" | ">"
          | "~"
          | "AFTER" | "ALT" | "AND" | "ANY" | "AT"
          | "BITAND" | "BITNOT" | "BITOR" | "BOOL" | "BYTE" | "BYTESIN"
          | "CASE" | "CHAN"
          | "DATA"
          | "ELSE"
          | "FALSE" | "FOR" | "FROM" | "FUNCTION"
          | "IF" | "IN" | "INLINE" | "INT" | "INT16" | "INT32" | "INT64"
          | "IS"
          | "MINUS" | "MOSTNEG" | "MOSTPOS"
          | "NOT"
          | "OF" | "OFFSETOF" | "OR"
          | "PACKED" | "PAR" | "PLACE" | "PLACED" | "PLUS" | "PORT"
          | "PRI" | "PROC" | "PROCESSOR" | "PROTOCOL"
          | "REAL32" | "REAL64" | "RECORD" | "REM" | "RESHAPES"
          | "RESULT" | "RETYPES" | "ROUND"
          | "SEQ" | "SIZE" | "SKIP" | "STOP"
          | "TIMER" | "TIMES" | "TRUE" | "TRUNC" | "TYPE"
          | "VAL" | "VALOF"
          | "WHILE" | "WORKSPACE"
          | "VECSPACE"
          | "#INCLUDE" | "#USE"

@identifier = [a-z A-Z] [a-z A-Z 0-9 \.]*

$escapeChar = [cnrts \" \' \* \n]
@escape = \* ( $escapeChar | \# $hexDigit $hexDigit )

@stringLiteral = \" ( @escape | [^\"] )* \"
@charLiteral = \' ( @escape | [^\'] ) \'

-- Note that occam number literals don't include their signs -- if you say
-- "-3", then that's the operator "-" applied to the literal "3".
@decimalLiteral = $decimalDigit+
@hexLiteral = "#" $hexDigit+
@exponent = ("+" | "-") $decimalDigit+
@realLiteral = ( $decimalDigit+ "." $decimalDigit+ "E" @exponent )
             | ( $decimalDigit+ "." $decimalDigit+ )

occam :-

-- Ignore whitespace and comments.
$white+            ;
"--" [^\n]*        ;

@reserved          { mkToken TokReserved }
@identifier        { mkToken TokIdentifier }

@stringLiteral     { mkToken TokStringLiteral }
@charLiteral       { mkToken TokCharLiteral }

@decimalLiteral    { mkToken TokDecimalLiteral }
@hexLiteral        { mkToken TokHexLiteral }
@realLiteral       { mkToken TokRealLiteral }

{
-- | An occam source token.
data Token = Token TokenType Meta String
  deriving (Show, Eq, Typeable, Data)

-- | The type of a source token.
data TokenType =
  TokReserved | TokIdentifier
  | TokStringLiteral | TokCharLiteral
  | TokDecimalLiteral | TokHexLiteral | TokRealLiteral
  deriving (Show, Eq, Typeable, Data)

-- | Build a lexer rule for a token.
mkToken :: TokenType -> AlexPosn -> String -> Token
mkToken tt (AlexPn _ line col) s = Token tt emptyMeta s

-- | Run the lexer, returning either an error position or a list of tokens.
-- (This is based on the `alexScanTokens` function that Alex provides, but it
-- adds error reporting.)
runLexer :: String -> String -> Either Meta [Token]
runLexer filename str = go (alexStartPos, '\n', str)
  where
    go inp@(pos@(AlexPn _ line col), _, str) =
         case alexScan inp 0 of
           AlexEOF -> Right []
           AlexError _ -> Left meta
           AlexSkip inp' len -> go inp'
           AlexToken inp' len act ->
             case go inp' of
               e@(Left _) -> e
               Right ts -> Right $ tok : ts
                             where (Token tt _ s) = act pos (take len str)
                                   tok = Token tt meta s

      where
        meta = emptyMeta {
                 metaFile = Just filename,
                 metaLine = line,
                 metaColumn = col
               }

-- | Main function for testing the lexer.
main :: IO ()
main
    =  do (arg:_) <- getArgs
          s <- readFile arg
          let tokens =
                case runLexer arg s of
                  Left m -> error $ "Lex error: " ++ show m
                  Right ts -> ts
          putStrLn $ pshow tokens
}

