module Main where

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Text.Megaparsec            hiding (State)

import           Data.Text                (Text)
import qualified Data.Text                as T
import qualified Data.Map.Strict          as M

import           System.Console.Haskeline

import           Core
import           Lang

process :: Text -> IO ()
process line = do
  let res = runParserT (runStateT (expr <* eof) (Ctx [] 0)) "" line
  case res of
    (Identity (Left e))      -> print e
    (Identity (Right (a,b))) -> do
      putStr "read: "
      print a
      let a' = eval a M.empty
      putStr "eval: "
      print a'
      putStr "print: "
      putStrLn $ T.unpack (pretty a')

main :: IO ()
main = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
    inp <- getInputLine "FMi>"
    case inp of
      Nothing   -> loop
      Just ":q" -> outputStrLn "Vale."
      Just i    -> (liftIO $ process (T.pack i)) >> loop




