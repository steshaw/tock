-- Demonstrate how to do unique naming.

import Control.Monad.State
import Data.Generics
import Data.List

--

data Name = Name String
  deriving (Show, Eq, Typeable, Data)

data Direction = Input Name | Output Name
  deriving (Show, Eq, Typeable, Data)

data Process = Declare Name Process | Use Direction | Seq [Process]
  deriving (Show, Eq, Typeable, Data)

--

type UniqueState = (Int, [(String, String)])
type UniqueM t = State UniqueState t

uniquelyName :: Process -> Process
uniquelyName p = evalState (doAny p) (0, [])

doAny :: Data t => t -> UniqueM t
doAny = doGeneric `extM` doName `extM` doProcess

doGeneric :: Data t => t -> UniqueM t
doGeneric = gmapM doAny

doProcess :: Process -> UniqueM Process
doProcess p = case p of
  Declare (Name n) _ -> do
    (count, vars) <- get
    put (count + 1, (n, n ++ "." ++ show count) : vars)
    p' <- doGeneric p
    (count', _) <- get
    put (count', vars)
    return p'
  otherwise -> doGeneric p

doName :: Name -> UniqueM Name
doName (Name s) = do
  (count, vars) <- get
  let s' = case lookup s vars of
             Just n -> n
             Nothing -> error $ "Name " ++ s ++ " not declared before use"
  return $ Name s'

--

demo :: Process -> IO ()
demo p = do
  putStrLn $ show p
  let p' = uniquelyName p
  putStrLn $ show p'
  putStrLn ""

main :: IO ()
main = do
  demo $ Declare (Name "foo") (Use (Input (Name "foo")))
  demo $ Declare (Name "a") (Seq [Use (Input (Name "a")),
                                  Use (Output (Name "a"))])
  demo $ Declare (Name "a") (Declare (Name "b") (Seq [Use (Input (Name "a")),
                                                      Use (Input (Name "b")),
                                                      Declare (Name "b") (Seq [Use (Input (Name "a")),
                                                                               Use (Input (Name "b"))])]))


