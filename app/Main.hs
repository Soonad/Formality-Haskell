{-# LANGUAGE FlexibleContexts #-}
module Main where

import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Control.Monad.Trans

import           Text.Megaparsec            hiding (State)

import           Data.List                  (isPrefixOf)
import qualified Data.Map.Strict            as M
import           Data.Text                  (Text)
import qualified Data.Text                  as T

import           System.Console.Repline
import           System.Process             (callCommand)

import           Core
import           Lang

type IState = M.Map Name Term
type Repl = HaskelineT (StateT IState IO)

-- Evaluation : handle each line user inputs
cmd :: Command Repl
cmd line = do
  let res = runParserT (runStateT (sc >> expr <* eof) (Ctx [] 0)) "" (T.pack line)
  case res of
    (Identity (Left e))      -> liftIO $ print e
    (Identity (Right (a,b))) -> do
      s <- get
      liftIO $ putStr "read: "
      liftIO $ print a
      let a' = eval a s
      let aT = runCheck (Env s []) (check a')
      --let aT = Right Typ
      case aT of
        Left e -> liftIO $ putStrLn (show e)
        Right aT -> do
          liftIO $ putStr "eval: "
          liftIO $ print a'
          liftIO $ putStr "print: "
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty a', " :: ", pretty aT]

-- Tab Completion: return a completion for partial words entered
completer :: (Monad m, MonadState IState m) => WordCompleter m
completer n = do
  ns <- gets M.keys
  return $ T.unpack <$> filter (T.isPrefixOf (T.pack n)) ns

-- Commands
help :: Cmd Repl
help args = liftIO $ print $ "Help: " ++ show args

quit :: Cmd Repl
quit args = liftIO (putStrLn "Goodbye.") >> abort

let_ :: Cmd Repl
let_ args =
  let line = unwords args
      res = runParserT (runStateT (sc >> def <* eof) (Ctx [] 0)) "" (T.pack line)
   in case res of
    (Identity (Left e))      -> liftIO $ print e
    (Identity (Right ((n,t),b))) -> do
      modify $ \s -> M.insert n t s
      liftIO $ putStr "read: "
      liftIO $ print t
      let a' = eval t M.empty
      let aT = runCheck (Env M.empty []) (check a')
      --let aT = Right Typ
      case aT of
        Left e -> liftIO $ putStrLn (show e)
        Right aT -> do
          liftIO $ putStr "eval: "
          liftIO $ print a'
          liftIO $ putStr "print: "
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty a', " :: ", pretty aT]

options :: Options Repl
options =
  [ ("help", help)
  , ("quit", quit)
  , ("let", let_)
  , ("q", quit)
  ]

ini :: Repl ()
ini = liftIO $ putStrLn "Welcome to Fide, the Formality interactive development environment!"

repl :: IO ()
repl = flip evalStateT M.empty $
  evalRepl (pure "Fide> ") cmd options (Just ':') (Word0 completer) ini

main :: IO ()
main = repl


