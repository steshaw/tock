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

-- | Lexically analyse Rain code.
module LexRain where

import Data.Generics

import Errors
import Metadata
import Pass
}

%wrapper "posn"

$decimalDigit = [0-9]
$hexDigit = [0-9 a-f A-F]

@reserved = "[" | "]" | "(" | ")" | "{" | "}"
          | ":" | "==" | "," | ";"
          | "?" | "!" | "=" | "+=" | "-=" | "*=" | "/=" | "%="
          | "+" | "-" | "*" | "/" | "%"
          | ">=" | "<="
          | "<" | ">"
          | ".."
          | "process" | "function" 
          | "pareach" | "seqeach" | "par" | "seq" 
          | "run" | "return"
          | "if" | "while" | "else"
          | "sint8" | "sint16" | "sint32" | "sint64"
          | "uint8" | "uint16" | "uint32" | "uint64"
          | "int" | "bool" | "channel"
          | "true" | "false"


@identifier = [a-z A-Z _] [a-z A-Z 0-9 _]*

$escapeChar = [cnrts \" \' \\ \n]
@escape = \\ ( $escapeChar | \# $hexDigit $hexDigit )

@stringLiteral = \" ( @escape | [^\\\"] )* \"
@charLiteral = \' ( @escape | [^\'] ) \'

@decimalLiteral = ("-")? $decimalDigit+
@hexLiteral = "#" $hexDigit+
@exponent = ("+" | "-") $decimalDigit+
@realLiteral = ("-")? ( $decimalDigit+ "." $decimalDigit+ "E" @exponent )
             | ( $decimalDigit+ "." $decimalDigit+ )

occam :-

-- Ignore whitespace and comments.
$white+            ;
"###" [^\n]*       ;

@reserved          { mkToken TokReserved }
@identifier        { mkToken TokIdentifier }

@stringLiteral     { mkTokenTrim TokStringLiteral }
@charLiteral       { mkTokenTrim TokCharLiteral }

@decimalLiteral    { mkToken TokDecimalLiteral }
@hexLiteral        { mkToken TokHexLiteral }
@realLiteral       { mkToken TokRealLiteral }

{
-- | An occam source token and its position.
type Token = (Meta, TokenType)

-- | An occam source token.
-- Only `Token` is generated by the lexer itself; the others are added later
-- once the indentation has been analysed.
data TokenType =
  TokReserved String                   -- ^ A reserved word or symbol
  | TokIdentifier String
  | TokStringLiteral String
  | TokCharLiteral String
  | TokDecimalLiteral String
  | TokHexLiteral String
  | TokRealLiteral String
  deriving (Show, Eq, Typeable, Data)

-- | Build a lexer rule for a token.
mkToken :: (String -> TokenType) -> AlexPosn -> String -> Token
mkToken cons _ s = (emptyMeta, cons s)

-- | Trims the beginning and end characters from a token -- useful for strings and chars
mkTokenTrim :: (String -> TokenType) -> AlexPosn -> String -> Token
mkTokenTrim cons _ s = (emptyMeta, cons (init (tail s)))

-- | Run the lexer, returning a list of tokens.
-- (This is based on the `alexScanTokens` function that Alex provides.)
runLexer :: String -> String -> IO (Either Meta [Token])
runLexer filename str = go (alexStartPos, '\n', str)
  where
    go inp@(pos@(AlexPn _ line col), _, str) =
         case alexScan inp 0 of
           AlexEOF -> return $ Right []
           AlexError _ -> return $ Left meta
           AlexSkip inp' len -> go inp'
           AlexToken inp' len act ->
             do ts <- go inp'
                let t = act pos (take len str)
                case ts of
                  Left m -> return $ Left m
                  Right toks -> return $ Right $ (meta, snd t) : toks

      where
        meta = Meta {
                 metaFile = Just filename,
                 metaLine = line,
                 metaColumn = col
               }
}

