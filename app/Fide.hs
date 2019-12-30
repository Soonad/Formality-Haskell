module Fide where

import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Control.Monad.Trans

import           Text.Megaparsec                         hiding (State)

import           Data.List                               (isPrefixOf)
import qualified Data.Map.Strict                         as M
import           Data.Text                               (Text)
import qualified Data.Text                               as T

import           System.Process                          (callCommand)

import qualified System.Console.Haskeline                as H
import           System.Console.Haskeline.Completion
import           System.Console.Haskeline.MonadException

import           Control.Applicative
import           Data.List                               (isPrefixOf)

import           Core
import           HaskelineT
import           Lang

type FideState = M.Map Name Term
type Repl = HaskelineT (StateT FideState IO)

repl :: (Functor m, MonadException m)      -- Terminal monad ( often IO ).
         => HaskelineT m Text              -- ^ prompt function
         -> HaskelineT m ()                -- ^ quit function
         -> (Text -> HaskelineT m ())      -- ^ process input function
         -> CompletionFunc m               -- ^ Tab completion function
         -> HaskelineT m a                 -- ^ Initialiser
         -> m ()
repl prompt quit process complete initial = runHaskelineT set (initial >> loop)
  where
    loop = do
      promptText <- prompt
      input <- H.handleInterrupt (return (Just "")) $ getInputLine promptText
      case input of
        Nothing    -> quit
        Just input
          | input == T.empty -> loop
          | otherwise -> H.handleInterrupt quit $ process input >> loop
    set = H.Settings
      { H.complete       = complete
      , H.historyFile    = Just ".history"
      , H.autoAddHistory = True
      }

prompt :: Repl Text
prompt = pure "Fide> "

quit :: Repl ()
quit = outputTxtLn "Goodbye."

data Command
  = Let Name Term
  | Eval Term
  | Quit
  | Help
  deriving (Eq, Show)

parseLine :: Parser Command
parseLine = do
   choice
     [ try $ (sym ":help" <|> sym ":h") >> return Help
     , try $ (sym ":quit" <|> sym ":q") >> return Quit
     , try $ do sym ":let"; (n,t) <- def; return $ Let n t
     , Eval <$> expr
     ]

process :: Text -> Repl ()
process line = do
  let res = runParserT (runStateT (sc >> parseLine <* eof) (Ctx [] 0)) "" line
  let unId (Identity x) = x
  case unId res of
    Left e      -> liftIO $ print e
    Right (Help,b)    -> do
      liftIO $ putStrLn "help text fills you with determination "
    Right (Quit,b)    -> abort
    Right (Let n t,b) -> do
      modify $ \s -> M.insert n t s
      s <- get
      liftIO $ putStr "read: "
      liftIO $ print t
      let a = eval t s
      let aT = runCheck (Env s []) (check a)
      case aT of
        Left e -> liftIO $ putStrLn (show e)
        Right aT -> do
          liftIO $ putStr "eval: "
          liftIO $ print a
          liftIO $ putStr "print: "
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty a, " :: ", pretty aT]
    Right (Eval t ,b) -> do
      s <- get
      liftIO $ putStr "read: "
      liftIO $ print t
      let a = eval t s
      let aT = runCheck (Env s []) (check a)
      case aT of
        Left e -> liftIO $ putStrLn (show e)
        Right aT -> do
          liftIO $ putStr "eval: "
          liftIO $ print a
          liftIO $ putStr "print: "
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty a, " :: ", pretty aT]

complete :: CompletionFunc (StateT FideState IO)
complete (ante, post) = do
  ns <- gets M.keys
  let keywords = [":quit", ":help", ":let"]
  let ns' = T.unpack <$> filter (T.isPrefixOf (T.pack ante)) (keywords ++ ns)
  return $ (post, simpleCompletion <$> ns')

fide :: StateT FideState IO ()
fide = repl prompt quit process complete ini
  where
    ini = liftIO $ putStrLn
      "Welcome to Fide, the Formality interactive development environment!"



