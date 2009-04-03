{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent
Copyright (C) 2008  Adam Sampson <ats@offog.org>

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

-- | Preprocess occam code.
module PreprocessOccam (preprocessOccamProgram, preprocessOccamSource,
                        preprocessOccam, expandIncludes) where

import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Numeric
import System.IO
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language (haskellDef)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.Regex

import CompState
import Errors
import LexOccam
import Metadata
import Pass
import PrettyShow
import StructureOccam
import Utils

-- | Open an included file, looking for it in the search path.
-- Return the open filehandle and the location of the file.
-- FIXME: This doesn't actually look at the search path yet.
searchFile :: Meta -> String -> PassM (Handle, String)
searchFile m filename
    =  do cs <- get
          let currentFile = csCurrentFile cs
          let possibilities = [joinPath currentFile filename]
          openOneOf possibilities
  where
    openOneOf :: [String] -> PassM (Handle, String)
    openOneOf [] = dieP m $ "Unable to find " ++ filename
    openOneOf (fn:fns)
        =  do r <- liftIO $ maybeIO $ openFile fn ReadMode
              case r of
                Just h -> return (h, fn)
                Nothing -> openOneOf fns

-- | Preprocess a file and return its tokenised form ready for parsing.
preprocessFile :: Meta -> String -> PassM [Token]
preprocessFile m filename
    =  do (handle, realFilename) <- searchFile m filename
          progress $ "Loading source file " ++ realFilename
          origCS <- get
          let modFunc = if drop9 filename `Set.member` csUsedFiles origCS
                          then Set.insert (drop9 realFilename)
                                 . Set.delete (drop9 filename)
                          else id
          modify (\cs -> cs { csCurrentFile = realFilename
                            , csUsedFiles = modFunc $ csUsedFiles cs })
          s <- liftIO $ hGetContents handle
          toks <- preprocessSource m realFilename s
          modify (\cs -> cs { csCurrentFile = csCurrentFile origCS })
          return toks
  where
    -- drops 9 (i.e. length ".tock.inc") from the end:
    drop9 = reverse . drop 9 . reverse

-- | Preprocesses source directly and returns its tokenised form ready for parsing.
preprocessSource :: Meta -> String -> String -> PassM [Token]
preprocessSource m realFilename s
    =  do toks <- runLexer realFilename s
          veryDebug $ "{{{ lexer tokens"
          veryDebug $ pshow toks
          veryDebug $ "}}}"
          toks' <- preprocessOccam toks
          veryDebug $ "{{{ preprocessed tokens"
          veryDebug $ pshow toks'
          veryDebug $ "}}}"
          toks'' <- structureOccam toks'
          veryDebug $ "{{{ structured tokens"
          veryDebug $ pshow toks''
          veryDebug $ "}}}"
          expandIncludes toks''

-- | Expand 'IncludeFile' markers in a token stream.
expandIncludes :: [Token] -> PassM [Token]
expandIncludes [] = return []
expandIncludes (Token m (IncludeFile filename) : Token _ EndOfLine : ts)
    =  do contents <- preprocessFile m filename
          rest <- expandIncludes ts
          return $ contents ++ rest
expandIncludes (Token m (IncludeFile _) : _)
    = error "IncludeFile token should be followed by EndOfLine"
expandIncludes (t:ts) = expandIncludes ts >>* (t :)

-- | Preprocess a token stream.
preprocessOccam :: [Token] -> PassM [Token]
preprocessOccam [] = return []
preprocessOccam (Token m (TokPreprocessor s) : ts)
    = handleDirective m (stripPrefix s) ts >>= preprocessOccam
  where
    stripPrefix :: String -> String
    stripPrefix (' ':cs) = stripPrefix cs
    stripPrefix ('\t':cs) = stripPrefix cs
    stripPrefix ('#':cs) = cs
    stripPrefix _ = error "bad TokPreprocessor prefix"
preprocessOccam (Token _ (TokReserved "##") : Token m (TokIdentifier var) : ts)
    =  do st <- get
          case Map.lookup var (csDefinitions st) of
            Just (PreprocInt num)    -> toToken $ TokIntLiteral num
            Just (PreprocString str) -> toToken $ TokStringLiteral str
            Just (PreprocNothing)    -> dieP m $ var ++ " is defined, but has no value"
            Nothing                  -> dieP m $ var ++ " is not defined"
  where
    toToken tt
        =  do rest <- preprocessOccam ts
              return $ Token m tt : rest
preprocessOccam (Token m (TokReserved "##") : _)
    = dieP m "Invalid macro expansion syntax"
preprocessOccam (t:ts)
    =  do rest <- preprocessOccam ts
          return $ t : rest

--{{{  preprocessor directive handlers
type DirectiveFunc = Meta -> [String] -> PassM ([Token] -> PassM [Token])

-- | Call the handler for a preprocessor directive.
handleDirective :: Meta -> String -> [Token] -> PassM [Token]
handleDirective m s x
  = do f <- lookup s directives
       f x
  where
    lookup :: String -> [(Regex, DirectiveFunc)] -> PassM ([Token] -> PassM [Token])
    -- FIXME: This should really be an error rather than a warning, but
    -- currently we support so few preprocessor directives that this is more
    -- useful.
    lookup s []
        =  do warnP m WarnUnknownPreprocessorDirective "Unknown preprocessor directive ignored"
              return return
    lookup s ((re, func):ds)
        = case matchRegex re s of
            Just fields -> func m fields
            Nothing -> lookup s ds

-- | List of handlers for preprocessor directives.
-- `handleDirective` walks down the regexps in this list until it finds one
-- that matches, then uses the corresponding function.
directives :: [(Regex, DirectiveFunc)]
directives =
  [ (mkRegex' "^INCLUDE +\"(.*)\"", handleInclude)
  , (mkRegex' "^USE +\"(.*)\"", handleUse)
  , (mkRegex "^COMMENT +.*$", handleIgnorable)
  , (mkRegex "^DEFINE +(.*)$", handleDefine)
  , (mkRegex "^UNDEF +([^ ]+)$", handleUndef)
  , (mkRegex "^IF +(.*)$", handleIf)
  , (mkRegex "^ELSE", handleUnmatched)
  , (mkRegex "^ENDIF", handleUnmatched)
  , (mkRegex "^PRAGMA +(.*)$", handlePragma)
  ]
  where
    mkRegex' s = mkRegex (s ++ " *(--.*)?$")

-- | Handle a directive that can be ignored.
handleIgnorable :: DirectiveFunc
handleIgnorable _ _ = return return

-- | Handle a directive that should have been removed as part of handling an
-- earlier directive.
handleUnmatched :: DirectiveFunc
handleUnmatched m _ = dieP m "Unmatched #ELSE/#ENDIF"

-- | Handle the @#INCLUDE@ directive.
handleInclude :: DirectiveFunc
handleInclude m (incName:_)
    = return (\ts -> return $ Token m (IncludeFile incName) : ts)

handlePragma :: DirectiveFunc
handlePragma m [pragma] = return (\ts -> return $ Token m (Pragma pragma) : ts)

-- | Handle the @#USE@ directive.
-- This is a bit of a hack at the moment, since it just includes the file
-- textually.
handleUse :: DirectiveFunc
handleUse m (modName:_)
    =  do let incName  = mangleModName modName
          cs <- get
          put $ cs { csUsedFiles = Set.insert incName (csUsedFiles cs) }
          if Set.member incName (csUsedFiles cs)
            then return return
            else handleInclude m [incName ++ ".tock.inc"]
  where
    -- | If a module name has a suffix, strip it
    mangleModName :: String -> String
    mangleModName mod
        = if ".occ" `isSuffixOf` mod || ".inc" `isSuffixOf` mod
            then (reverse . drop 4 . reverse) mod
            else mod

-- | Handle the @#DEFINE@ directive.
handleDefine :: DirectiveFunc
handleDefine m [definition]
    =  do (var, value) <- runPreprocParser m defineDirective definition
          st <- get
          when (Map.member var $ csDefinitions st) $
            dieP m $ "Preprocessor symbol is already defined: " ++ var
          put $ st { csDefinitions = Map.insert var value $ csDefinitions st }
          return return

-- | Handle the @#UNDEF@ directive.
handleUndef :: DirectiveFunc
handleUndef m [var]
    =  do modify $ \st -> st { csDefinitions = Map.delete var $ csDefinitions st }
          return return

-- | Handle the @#IF@ directive.
handleIf :: DirectiveFunc
handleIf m [condition]
    =  do b <- runPreprocParser m expression condition
          return $ skipCondition b 0
  where
    skipCondition :: Bool -> Int -> [Token] -> PassM [Token]
    skipCondition _ _ [] = dieP m "Couldn't find a matching #ENDIF"

    -- At level 0, we flip state on ELSE and finish on ENDIF.
    skipCondition b 0 (t@(Token _ (TokPreprocessor pp)) : ts)
        | "#IF" `isPrefixOf` pp       = skipCondition b 1 ts >>* (t :)
        | "#ELSE" `isPrefixOf` pp     = skipCondition (not b) 0 ts
        | "#ENDIF" `isPrefixOf` pp    = return ts
        | otherwise                   = copyThrough b 0 t ts

    -- At higher levels, we just count up and down on IF and ENDIF.
    skipCondition b n (t@(Token _ (TokPreprocessor pp)) : ts)
        | "#IF" `isPrefixOf` pp       = skipCondition b (n + 1) ts >>* (t :)
        | "#ENDIF" `isPrefixOf` pp    = skipCondition b (n - 1) ts >>* (t :)
        | otherwise                   = copyThrough b n t ts

    -- And otherwise we copy through tokens if the condition's true.
    skipCondition b n (t:ts) = copyThrough b n t ts

    copyThrough :: Bool -> Int -> Token -> [Token] -> PassM [Token]
    copyThrough True n t ts = skipCondition True n ts >>* (t :)
    copyThrough False n _ ts = skipCondition False n ts
--}}}

--{{{  parser for preprocessor expressions
type PreprocParser = GenParser Char (Map.Map String PreprocDef)

--{{{  lexer
reservedOps :: [String]
reservedOps = ["=", "<>", "<", "<=", ">", ">="]

ppLexer :: P.TokenParser (Map.Map String PreprocDef)
ppLexer = P.makeTokenParser (haskellDef
  { P.identStart = letter <|> digit
  , P.identLetter = letter <|> digit <|> char '.'
  , P.reservedOpNames = reservedOps
  })

lexeme :: PreprocParser a -> PreprocParser a
lexeme = P.lexeme ppLexer

whiteSpace :: PreprocParser ()
whiteSpace = P.whiteSpace ppLexer

identifier :: PreprocParser String
identifier = P.identifier ppLexer

parens :: PreprocParser a -> PreprocParser a
parens = P.parens ppLexer

symbol :: String -> PreprocParser String
symbol = P.symbol ppLexer

reservedOp :: String -> PreprocParser ()
reservedOp = P.reservedOp ppLexer
--}}}

tryVX :: PreprocParser a -> PreprocParser b -> PreprocParser a
tryVX a b = try (do { av <- a; b; return av })

tryVV :: PreprocParser a -> PreprocParser b -> PreprocParser (a, b)
tryVV a b = try (do { av <- a; bv <- b; return (av, bv) })

literal :: PreprocParser PreprocDef
literal
    =   (lexeme $ do { ds <- many1 digit; return $ PreprocInt ds })
    <|> (lexeme $ do { char '"'; s <- manyTill anyChar $ char '"'; return $ PreprocString s })
    <?> "preprocessor literal"

defineDirective :: PreprocParser (String, PreprocDef)
defineDirective
    =  do whiteSpace
          var <- identifier
          value <- option PreprocNothing literal
          eof
          return (var, value)
    <?> "preprocessor definition"

defined :: PreprocParser Bool
defined
    =  do symbol "DEFINED"
          var <- parens identifier
          definitions <- getState
          return $ Map.member var definitions

simpleExpression :: PreprocParser Bool
simpleExpression
    =   do { try $ symbol "NOT"; e <- expression; return $ not e }
    <|> do { try $ symbol "TRUE"; return True }
    <|> do { try $ symbol "FALSE"; return False }
    <|> defined
    <|> parens expression
    <?> "preprocessor simple expression"

operand :: PreprocParser PreprocDef
operand
    =   literal
    <|> do var <- identifier
           definitions <- getState
           case Map.lookup var definitions of
             Nothing             -> fail $ var ++ " is not defined"
             Just PreprocNothing -> fail $ var ++ " is defined, but has no value"
             Just value          -> return value
    <?> "preprocessor operand"

comparisonOp :: PreprocParser String
comparisonOp
    = choice [do { try $ reservedOp op; return op } | op <- reservedOps]
    <?> "preprocessor comparison operator"

-- | Apply a comparison operator to two values, checking the types are
-- appropriate.
applyComparison :: String -> PreprocDef -> PreprocDef -> PreprocParser Bool
applyComparison op (PreprocString l) (PreprocString r)
    = case op of
        "="  -> return $ l == r
        "<>" -> return $ l /= r
        _    -> fail "Invalid operator for string comparison"
applyComparison op (PreprocInt l) (PreprocInt r)
    =  do lv <- getInt l
          rv <- getInt r
          case op of
            "="  -> return $ lv == rv
            "<>" -> return $ lv /= rv
            "<"  -> return $ lv < rv
            "<=" -> return $ lv <= rv
            ">"  -> return $ lv > rv
            ">=" -> return $ lv >= rv
  where
    getInt :: String -> PreprocParser Int
    getInt s
        = case readDec s of
            [(v, "")] -> return v
            _ -> fail $ "Bad integer literal: " ++ s
applyComparison _ _ _ = fail "Invalid types for comparison"

expression :: PreprocParser Bool
expression
    =   do { l <- tryVX simpleExpression (symbol "AND"); r <- simpleExpression; return $ l && r }
    <|> do { l <- tryVX simpleExpression (symbol "OR"); r <- simpleExpression; return $ l || r }
    <|> do { (l, op) <- tryVV operand comparisonOp; r <- operand; applyComparison op l r }
    <|> simpleExpression
    <?> "preprocessor complex expression"

-- | Match a 'PreprocParser' production.
runPreprocParser :: Meta -> PreprocParser a -> String -> PassM a
runPreprocParser m prod s
    =  do st <- get
          case runParser wrappedProd (csDefinitions st) (show m) s of
            Left err -> dieP m $ "Error parsing preprocessor instruction: " ++ show err
            Right b -> return b
  where
    wrappedProd
       = do whiteSpace
            v <- prod
            eof
            return v
--}}}

-- | Load and preprocess an occam program.
preprocessOccamProgram :: String -> PassM [Token]
preprocessOccamProgram filename
    =  do toks <- preprocessFile emptyMeta filename
          -- Leave the main file name in the csCurrentFile slot:
          modify $ \cs -> cs { csCurrentFile = filename }
          veryDebug $ "{{{ tokenised source"
          veryDebug $ pshow toks
          veryDebug $ "}}}"
          return toks

-- | Preprocesses occam source direct from the given String
preprocessOccamSource :: String -> PassM [Token]
preprocessOccamSource source = preprocessSource emptyMeta "<unknown>" source
