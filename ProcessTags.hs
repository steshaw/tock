import Control.Monad
import Data.List

data Section = Section String [String]

instance Show Section where
  show (Section fileName lines)
    = unlines ["\x0c", fileName ++ "," ++ show (length ls)]
      ++ ls
    where
      ls = unlines lines

splitIntoSections :: [String] -> [Section]
splitIntoSections ("\x0c" : fileLine : rest)
  = (Section (takeWhile (/= ',') fileLine) this)
      : splitIntoSections next
  where
    (this, next) = span (/= "\x0c") rest
splitIntoSections [] = []
splitIntoSections (l:_) = error $ "Unexpected line: " ++ l

getPrefix :: [String] -> String -> (String, String)
getPrefix ps s = head $ [ (p, drop (length p) s)
                        | p <- ps, p `isPrefixOf` s]
                        ++ [([], s)] -- default option

data LinePart = WhiteSpacePunctuation String | Keyword String | Identifier String

lineParts :: String -> [LinePart]
lineParts [] = []
lineParts s = case filter (not . null . fst . fst) $
                     [(span (`notElem` wordChars) s, WhiteSpacePunctuation)
                     ,(getPrefix keywords s, Keyword)
                     ,(span (`elem` wordChars) s, Identifier)] of
                (((pre, post), f):_) -> f pre : lineParts post
                _ -> error $ "Could not parse line: " ++ s
  where
    wordChars = ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ ['\'','_']
    keywords = ["let","data","type","newtype"]

qualify :: String -> String -> String
qualify modName line
  = concat [case lp of
              WhiteSpacePunctuation s -> s
              Keyword k -> k
              Identifier s -> s
           | lp <- lineParts lineStart]
           ++ "\x7f"
           ++ concat [prefix s ++ "\x01" | Identifier s <- lineParts lineStart]
           ++ tail lineEnd
  where
    prefix = ((modName ++ ".") ++)
    (lineStart, lineEnd) = span (/= '\x7f') line

main :: IO ()
main = do ls <- liftM lines $ getContents
          let lsSplit = splitIntoSections ls
              lsSplit' = [ if fileName == "data/AST.hs"
                              then Section fileName $ map (qualify "A") lines
                              else Section fileName lines
                         | Section fileName lines <- lsSplit]
          putStr (concatMap show lsSplit')
