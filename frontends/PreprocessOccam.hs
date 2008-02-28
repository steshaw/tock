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
module PreprocessOccam (preprocessOccamProgram, preprocessOccamSource, preprocessOccam) where

import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
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
          modify (\cs -> cs { csCurrentFile = realFilename })
          s <- liftIO $ hGetContents handle
          toks <- preprocessSource m realFilename s
          modify (\cs -> cs { csCurrentFile = csCurrentFile origCS })
          return toks
          
-- | Preprocesses source directly and returns its tokenised form ready for parsing.
preprocessSource :: Meta -> String -> String -> PassM [Token]
preprocessSource m realFilename s
    =  do toks <- runLexer realFilename s
          veryDebug $ "{{{ lexer tokens"
          veryDebug $ pshow toks
          veryDebug $ "}}}"
          toks' <- structureOccam toks
          veryDebug $ "{{{ structured tokens"
          veryDebug $ pshow toks'
          veryDebug $ "}}}"
          toks'' <- preprocessOccam toks'
          veryDebug $ "{{{ preprocessed tokens"
          veryDebug $ pshow toks''
          veryDebug $ "}}}"
          return toks''

-- | Preprocess a token stream.
preprocessOccam :: [Token] -> PassM [Token]
preprocessOccam [] = return []
preprocessOccam ((m, TokPreprocessor s):(_, EndOfLine):ts)
    =  do (beforeRest, afterRest) <- handleDirective m (stripPrefix s)
          rest <- beforeRest ts >>= preprocessOccam
          return $ afterRest rest
  where
    stripPrefix :: String -> String
    stripPrefix (' ':cs) = stripPrefix cs
    stripPrefix ('\t':cs) = stripPrefix cs
    stripPrefix ('#':cs) = cs
    stripPrefix _ = error "bad TokPreprocessor prefix"
-- Check the above case didn't miss something.
preprocessOccam ((_, TokPreprocessor _):_)
    = error "bad TokPreprocessor token"
preprocessOccam ((_, TokReserved "##") : (m, TokIdentifier var) : ts)
    =  do st <- get
          case Map.lookup var (csDefinitions st) of
            Just (PreprocInt num)    -> toToken $ TokIntLiteral num
            Just (PreprocString str) -> toToken $ TokStringLiteral str
            Just (PreprocNothing)    -> dieP m $ var ++ " is defined, but has no value"
            Nothing                  -> dieP m $ var ++ " is not defined"
  where
    toToken tt
        =  do rest <- preprocessOccam ts
              return $ (m, tt) : rest
preprocessOccam ((m, TokReserved "##"):_)
    = dieP m "Invalid macro expansion syntax"
preprocessOccam (t:ts)
    =  do rest <- preprocessOccam ts
          return $ t : rest

--{{{  preprocessor directive handlers
type DirectiveFunc = Meta -> [String] -> PassM ([Token] -> PassM [Token], [Token] -> [Token])

-- | Call the handler for a preprocessor directive.
handleDirective :: Meta -> String -> PassM ([Token] -> PassM [Token], [Token] -> [Token])
handleDirective m s = lookup s directives
  where
    -- FIXME: This should really be an error rather than a warning, but
    -- currently we support so few preprocessor directives that this is more
    -- useful.
    lookup s []
        =  do addWarning m "Unknown preprocessor directive ignored"
              return (return, id)
    lookup s ((re, func):ds)
        = case matchRegex re s of
            Just fields -> func m fields
            Nothing -> lookup s ds

-- | List of handlers for preprocessor directives.
-- `handleDirective` walks down the regexps in this list until it finds one
-- that matches, then uses the corresponding function.
directives :: [(Regex, DirectiveFunc)]
directives =
  [ (mkRegex "^INCLUDE +\"(.*)\"$", handleInclude)
  , (mkRegex "^USE +\"(.*)\"$", handleUse)
  , (mkRegex "^COMMENT +.*$", handleIgnorable)
  , (mkRegex "^DEFINE +(.*)$", handleDefine)
  , (mkRegex "^UNDEF +([^ ]+)$", handleUndef)
  , (mkRegex "^IF +(.*)$", handleIf)
  , (mkRegex "^ELSE", handleUnmatched)
  , (mkRegex "^ENDIF", handleUnmatched)
  ]

-- | Handle a directive that can be ignored.
handleIgnorable :: DirectiveFunc
handleIgnorable _ _ = return (return, id)

-- | Handle a directive that should have been removed as part of handling an
-- earlier directive.
handleUnmatched :: DirectiveFunc
handleUnmatched m _ = dieP m "Unmatched #ELSE/#ENDIF"

-- | Handle the @#INCLUDE@ directive.
handleInclude :: DirectiveFunc
handleInclude m [incName]
    =  do toks <- preprocessFile m incName
          return (return, \ts -> toks ++ ts)

-- | Handle the @#USE@ directive.
-- This is a bit of a hack at the moment, since it just includes the file
-- textually.
handleUse :: DirectiveFunc
handleUse m [modName]
    =  do let incName  = mangleModName modName
          cs <- get
          put $ cs { csUsedFiles = Set.insert incName (csUsedFiles cs) }
          if Set.member incName (csUsedFiles cs)
            then return (return, id)
            else handleInclude m [incName]
  where
    -- | If a module name doesn't already have a suffix, add one.
    mangleModName :: String -> String
    mangleModName mod
        = if ".occ" `isSuffixOf` mod || ".inc" `isSuffixOf` mod
            then mod
            else mod ++ ".occ"

-- | Handle the @#DEFINE@ directive.
handleDefine :: DirectiveFunc
handleDefine m [definition]
    =  do (var, value) <- lookup definition definitionTypes
          st <- get
          when (Map.member var $ csDefinitions st) $
            dieP m $ "Preprocessor symbol is already defined: " ++ var
          put $ st { csDefinitions = Map.insert var value $ csDefinitions st }
          return (return, id)
  where
    definitionTypes :: [(Regex, [String] -> (String, PreprocDef))]
    definitionTypes =
      [ (mkRegex "^([^ ]+)$",           (\[name]      -> (name, PreprocNothing)))
      , (mkRegex "^([^ ]+) +([0-9]+)$", (\[name, num] -> (name, PreprocInt num)))
      , (mkRegex "^([^ ]+) \"(.*)\"$",  (\[name, str] -> (name, PreprocString str)))
      ]

    lookup s [] = dieP m "Invalid definition syntax"
    lookup s ((re, func):ds)
        = case matchRegex re s of
            Just fields -> return $ func fields
            Nothing -> lookup s ds

-- | Handle the @#UNDEF@ directive.
handleUndef :: DirectiveFunc
handleUndef m [var]
    =  do modify $ \st -> st { csDefinitions = Map.delete var $ csDefinitions st }
          return (return, id)

-- | Handle the @#IF@ directive.
handleIf :: DirectiveFunc
handleIf m [condition]
    =  do b <- evalExpression m condition
          return (skipCondition b 0, id)
  where
    skipCondition :: Bool -> Int -> [Token] -> PassM [Token]
    skipCondition _ _ [] = dieP m "Couldn't find a matching #ENDIF"

    -- At level 0, we flip state on ELSE and finish on ENDIF.
    skipCondition b 0 (t1@(_, TokPreprocessor pp) : t2@(_, EndOfLine) : ts)
        | "#IF" `isPrefixOf` pp       = skipCondition b 1 ts >>* (\ts -> t1 : t2 : ts)
        | "#ELSE" `isPrefixOf` pp     = skipCondition (not b) 0 ts
        | "#ENDIF" `isPrefixOf` pp    = return ts
        | otherwise                   = copyThrough b 0 ((t1 :) . (t2 :)) ts

    -- At higher levels, we just count up and down on IF and ENDIF.
    skipCondition b n (t1@(_, TokPreprocessor pp) : t2@(_, EndOfLine) : ts)
        | "#IF" `isPrefixOf` pp       = skipCondition b (n + 1) ts >>* (\ts -> t1 : t2 : ts)
        | "#ENDIF" `isPrefixOf` pp    = skipCondition b (n - 1) ts >>* (\ts -> t1 : t2 : ts)
        | otherwise                   = copyThrough b n ((t1 :) . (t2 :)) ts

    -- And otherwise we copy through tokens if the condition's true.
    skipCondition b n (t:ts) = copyThrough b n (t :) ts

    copyThrough :: Bool -> Int -> ([Token] -> [Token]) -> [Token] -> PassM [Token]
    copyThrough True n f ts = skipCondition True n ts >>* f
    copyThrough False n _ ts = skipCondition False n ts
--}}}

--{{{  parser for preprocessor expressions
type PreprocParser = GenParser Char (Map.Map String PreprocDef)

--{{{  lexer
ppLexer :: P.TokenParser (Map.Map String PreprocDef)
ppLexer = P.makeTokenParser (haskellDef
  { P.identStart = letter <|> digit
  , P.identLetter = letter <|> digit <|> char '.'
  })

parens :: PreprocParser a -> PreprocParser a
parens = P.parens ppLexer

symbol :: String -> PreprocParser String
symbol = P.symbol ppLexer
--}}}

tryVX :: PreprocParser a -> PreprocParser b -> PreprocParser a
tryVX a b = try (do { av <- a; b; return av })

defined :: PreprocParser Bool
defined
    =  do symbol "DEFINED"
          i <- parens $ P.identifier ppLexer
          definitions <- getState
          return $ Map.member i definitions

operand :: PreprocParser Bool
operand
    =   do { try $ symbol "NOT"; e <- expression; return $ not e }
    <|> do { try $ symbol "TRUE"; return True }
    <|> do { try $ symbol "FALSE"; return False }
    <|> defined
    <|> parens expression
    <?> "preprocessor operand"

expression :: PreprocParser Bool
expression
    =   do { l <- tryVX operand (symbol "AND"); r <- operand; return $ l && r }
    <|> do { l <- tryVX operand (symbol "OR"); r <- operand; return $ l || r }
    <|> operand
    <?> "preprocessor expression"

fullExpression :: PreprocParser Bool
fullExpression
    =  do P.whiteSpace ppLexer
          e <- expression
          eof
          return e

-- | Evaluate a preprocessor expression.
evalExpression :: Meta -> String -> PassM Bool
evalExpression m s
    =  do st <- get
          case runParser fullExpression (csDefinitions st) (show m) s of
            Left err -> dieP m $ "Error parsing expression: " ++ show err
            Right b -> return b
--}}}

-- | Load and preprocess an occam program.
preprocessOccamProgram :: String -> PassM [Token]
preprocessOccamProgram filename
    =  do toks <- preprocessFile emptyMeta filename
          veryDebug $ "{{{ tokenised source"
          veryDebug $ pshow toks
          veryDebug $ "}}}"
          return toks

-- | Preprocesses occam source direct from the given String
preprocessOccamSource :: String -> PassM [Token]
preprocessOccamSource source = preprocessSource emptyMeta "<unknown>" source
