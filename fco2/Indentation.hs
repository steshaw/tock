-- | Parse indentation in occam source.
module Indentation (removeIndentation, indentMarker, outdentMarker, eolMarker) where

import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Data.List
import Text.Regex

import CompState
import Errors
import Pass

-- FIXME When this joins continuation lines, it should stash the details of
-- what it joined into CompState so that error reporting later on can
-- reconstruct the original position.

indentMarker = "__indent"
outdentMarker = "__outdent"
eolMarker = "__eol"

-- FIXME: There's probably a nicer way of doing this.
-- (Well, trivially, use a WriterT...)

-- | Preprocess occam source code to remove comments and turn indentation into
-- explicit markers.
removeIndentation :: String -> String -> PassM String
removeIndentation filename orig
    =  do modify $ (\ps -> ps { csIndentLinesIn = origLines,
                                csIndentLinesOut = [] })
          catchError (nextLine 0) reportError
          ps <- get
          let out = concat $ intersperse "\n" $ reverse $ csIndentLinesOut ps
          modify $ (\ps -> ps { csIndentLinesIn = [],
                                csIndentLinesOut = [] })
          return out
  where
    origLines = lines orig

    -- | When something goes wrong, figure out how far through the file we'd got.
    reportError :: String -> PassM ()
    reportError error
        =  do ps <- get
              let lineNumber = length origLines - length (csIndentLinesIn ps)
              die $ filename ++ ":" ++ show lineNumber ++ ": " ++ error

    -- | Get the next raw line from the input.
    getLine :: PassM (Maybe String)
    getLine
        =  do ps <- get
              case csIndentLinesIn ps of
                [] -> return Nothing
                (line:rest) ->
                  do put $ ps { csIndentLinesIn = rest }
                     return $ Just line

    -- | Add a line to the output.
    putLine :: String -> PassM ()
    putLine line
        = modify $ (\ps -> ps { csIndentLinesOut = line : csIndentLinesOut ps })

    -- | Append to the *previous* line added.
    addToLine :: String -> PassM ()
    addToLine s
        = modify $ (\ps -> ps { csIndentLinesOut =
                                  case csIndentLinesOut ps of (l:ls) -> ((l ++ s):ls) })

    -- | Given a line, read the rest of it, then return the complete thing.
    finishLine :: String -> String -> Bool -> Bool -> String -> PassM String
    finishLine left soFar inStr isChar afterStr
        = case (left, inStr, isChar) of
            ([], False, _) -> plainEOL
            ('-':'-':cs, False, _) -> plainEOL
            ([], True, _) -> die "end of line in string without continuation"
            (['*'], True, _) -> stringEOL
            ('\'':cs, False, _) -> finishLine cs (afterStr ++ ('\'':soFar)) True True ""
            ('\'':cs, True, True) -> finishLine cs (afterStr ++ ('\'':soFar)) False False ""
            ('"':cs, False, _) -> finishLine cs (afterStr ++ ('"':soFar)) True False ""
            ('"':cs, True, False) -> finishLine cs (afterStr ++ ('"':soFar)) False False ""
            ('*':'*':cs, True, _) -> finishLine cs ('*':'*':soFar) True isChar afterStr
            ('*':'"':cs, True, _) -> finishLine cs ('"':'*':soFar) True isChar afterStr
            ('*':'\'':cs, True, _) -> finishLine cs ('\'':'*':soFar) True isChar afterStr
            (c:cs, _, _) -> finishLine cs (c:soFar) inStr isChar afterStr
      where
        -- | Finish a regular line.
        plainEOL :: PassM String
        plainEOL
            =  do let s = reverse soFar
                  if hasContinuation s
                    then do l <- getLine >>= checkJust "no continuation line"
                            finishLine l ('\n':soFar) False False ""
                    else return s

        -- | Finish a line where we're in the middle of a string.
        stringEOL :: PassM String
        stringEOL
            =  do l <- getLine >>= checkJust "no string continuation line"
                  l' <- contStringStart l
                  -- When we hit the end of the string, add a \n after it to
                  -- make the line numbers match up again.
                  finishLine l' soFar True isChar ('\n':afterStr)

    -- | Does a line have a continuation line following it?
    hasContinuation :: String -> Bool
    hasContinuation s
        = case matchRegex contRE s of
            Just _ -> True
            Nothing -> False
      where
        -- FIXME This should probably be based on the list of operators and
        -- reserved words that the parser already has; for now this is the
        -- regexp that occamdoc uses.
        contRE = mkRegexWithOpts "(-|~|\\+|-|\\*|/|\\\\|/\\\\|\\\\/|><|=|<>|<|>|>=|<=|,|;|:=|<<|>>|([[:space:]](MINUS|BITNOT|NOT|SIZE|REM|PLUS|MINUS|TIMES|BITAND|BITOR|AND|OR|AFTER|FROM|FOR|IS|RETYPES|RESHAPES)))[[:space:]]*$" False True

    -- | Strip the spaces-then-star beginning off a string continuation line.
    contStringStart :: String -> PassM String
    contStringStart (' ':cs) = contStringStart cs
    contStringStart ('*':cs) = return cs
    contStringStart _ = die "string continuation line doesn't start with *"

    -- | Get the next *complete* line from the input, resolving continuations.
    readLine :: PassM (Maybe String)
    readLine
        =  do line <- getLine
              case line of
                Just s ->
                  do r <- finishLine s "" False False ""
                     return $ Just r
                Nothing -> return Nothing

    -- | Compute the indentation level of a line, and return it without the indentation.
    countIndent :: String -> Int -> PassM (Int, String)
    -- Tabs are 8 spaces.
    countIndent ('\t':cs) soFar = countIndent cs (soFar + 4)
    countIndent (' ':' ':cs) soFar = countIndent cs (soFar + 1)
    countIndent [' '] soFar = return (soFar, [])
    countIndent (' ':_) soFar
        = die "bad indentation (odd number of spaces)"
    countIndent cs soFar = return (soFar, cs)

    -- | Repeat a string N times.
    rep :: Int -> String -> String
    rep n s = concat $ take n (repeat s)

    -- | Process the next line from the input.
    nextLine :: Int -> PassM ()
    nextLine level
        =  do l <- readLine
              case l of
                Nothing -> return ()
                Just line ->
                  do (newLevel, stripped) <- countIndent line 0
                     addLine level newLevel line stripped

    -- | Once a line's been retrieved, add it to the output along with the
    -- appropriate markers, then go and process the next one.
    addLine :: Int -> Int -> String -> String -> PassM ()
    addLine level newLevel line stripped
      | stripped == "" =
        do putLine ""
           nextLine level
      | newLevel > level =
        do addToLine $ rep (newLevel - level) (" " ++ indentMarker)
           putLine $ line ++ " " ++ eolMarker
           nextLine newLevel
      | newLevel < level =
        do addToLine $ rep (level - newLevel) (" " ++ outdentMarker)
           putLine $ line ++ " " ++ eolMarker
           nextLine newLevel
      | otherwise =
        do putLine $ line ++ " " ++ eolMarker
           nextLine level

