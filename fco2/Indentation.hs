-- | Parse indentation in occam source.
module Indentation (removeIndentation, indentMarker, outdentMarker, eolMarker) where

import Control.Monad
import Control.Monad.State
import Data.List

import Errors
import ParseState
import Pass

-- FIXME When this joins continuation lines, it should stash the details of
-- what it joined into ParseState so that error reporting later on can
-- reconstruct the original position.

-- FIXME this doesn't handle multi-line strings
-- FIXME or VALOF processes
-- FIXME or continuation lines...

indentMarker = "__indent"
outdentMarker = "__outdent"
eolMarker = "__eol"

-- FIXME: There's probably a nicer way of doing this.
-- (Well, trivially, use a WriterT...)

removeIndentation :: String -> PassM String
removeIndentation orig
    =  do modify $ (\ps -> ps { psIndentLinesIn = lines orig,
                                psIndentLinesOut = [] })
          -- FIXME Catch errors and figure out the source position based on the
          -- input lines.
          nextLine 0
          ps <- get
          let out = concat $ intersperse "\n" $ reverse $ psIndentLinesOut ps
          modify $ (\ps -> ps { psIndentLinesIn = [],
                                psIndentLinesOut = [] })
          return out
  where
    -- | Get the next raw line from the input.
    getLine :: PassM (Maybe String)
    getLine
        =  do ps <- get
              case psIndentLinesIn ps of
                [] -> return Nothing
                (line:rest) ->
                  do put $ ps { psIndentLinesIn = rest }
                     return $ Just line

    -- | Add a line to the output.
    putLine :: String -> PassM ()
    putLine line
        = modify $ (\ps -> ps { psIndentLinesOut = line : psIndentLinesOut ps })

    -- | Append to the *previous* line added.
    addToLine :: String -> PassM ()
    addToLine s
        = modify $ (\ps -> ps { psIndentLinesOut =
                                  case psIndentLinesOut ps of (l:ls) -> ((l ++ s):ls) })

    -- | Given a line, read the rest of it, then return the complete thing.
    finishLine :: String -> String -> Bool -> PassM String
    finishLine left soFar inStr
        = case (left, inStr) of
            ([], False) -> plainEOL
            ('-':'-':cs, False) -> plainEOL
            ([], True) -> die "end of line in string without continuation"
            (['*'], True) -> stringEOL
            ('"':cs, iS) -> finishLine cs ('"':soFar) (not iS)
            ('*':'"':cs, True) -> finishLine cs ('"':'*':soFar) True
            (c:cs, iS) -> finishLine cs (c:soFar) iS
      where
        -- FIXME check if this should have a continuation
        plainEOL = return $ reverse soFar
        -- FIXME implement
        stringEOL = die "string continues"

    -- | Get the next *complete* line from the input, resolving continuations.
    readLine :: PassM (Maybe String)
    readLine
        =  do line <- getLine
              case line of
                Just s ->
                  do r <- finishLine s "" False
                     return $ Just r
                Nothing -> return Nothing

    -- | Compute the indentation level of a line, and return it without the indentation.
    countIndent :: String -> Int -> PassM (Int, String)
    -- Tabs are 8 spaces.
    countIndent ('\t':cs) soFar = countIndent cs (soFar + 4)
    countIndent (' ':' ':cs) soFar = countIndent cs (soFar + 1)
    countIndent (' ':cs) soFar
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
                     addLine level newLevel stripped

    -- | Once a line's been retrieved, add it to the output along with the
    -- appropriate markers, then go and process the next one.
    addLine :: Int -> Int -> String -> PassM ()
    addLine level newLevel line
      | line == "" =
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

