module Fide where

import           Control.Applicative
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

import           Check
import           Core
import           HaskelineT
import           Lang
import           Pretty

data FideST = FideST
  { topDefs :: M.Map Name Term
  }

type Repl = HaskelineT (StateT FideST IO)

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
  | Load FilePath
  | Quit
  | Help
  | Refs
  deriving (Eq, Show)

parseLine :: Parser Command
parseLine = do
   choice
     [ try $ (sym ":help" <|> sym ":h") >> return Help
     , try $ (sym ":quit" <|> sym ":q") >> return Quit
     , try $ do sym ":let"; (n,t) <- sc >> def; return $ Let n t
     , try $ do (sym ":load" <|> sym ":l"); (Load . T.unpack) <$> filename <* sc
     , try $ do (sym ":refs"); return Refs
     , try $ do (n,t) <- sc >> def; return $ Let n t
     , Eval <$> expr
     ]

filename :: Parser Text
filename = takeWhile1P Nothing (\s -> s /= ' ')

process :: Text -> Repl ()
process line = do
  let res = runParserT (runStateT (sc >> parseLine <* eof) (Ctx [] 0)) "" line
  let unId (Identity x) = x
  case unId res of
    Left e      -> liftIO $ print e
    Right (Refs,b)    -> do
      ds <- gets topDefs
      liftIO $ print ds
    Right (Help,b)    -> do
      liftIO $ putStrLn "help text fills you with determination "
    Right (Quit,b)    -> abort
    Right (Load f,b) -> do
      fileText <- liftIO $ readFile f
      let res = runParserT (runStateT (file <* eof) (Ctx [] 0)) "" (T.pack fileText)
      case unId res of
        Left e      -> liftIO $ print e
        Right (defs,b) -> do
          liftIO $ putStrLn $ "Loaded "  ++ f
          modify $ \s -> s { topDefs = defs }
    Right (Let n t,b) -> do
      modify $ \s -> s { topDefs = M.insert n t (topDefs s) }
      ds <- gets topDefs
      liftIO $ putStr "read: "
      liftIO $ print t
      let tT = checkTerm t
      case tT of
        (Left e, st, logs) -> do
          liftIO $ putStr "ERROR: " >> putStrLn (show e)
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
        (Right tT, st, logs) -> do
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty t, " :: ", pretty tT]
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
      let a = eval t ds
      let aT = checkTerm a
      case aT of
        (Left e, st, logs) -> do
          liftIO $ putStr "ERROR: " >> putStrLn (show e)
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
        (Right aT, st, logs) -> do
          liftIO $ putStr "eval: "
          liftIO $ print a
          liftIO $ putStr "print: "
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty a, " :: ", pretty aT]
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
    Right (Eval t ,b) -> do
      ds <- gets topDefs
      liftIO $ putStr "read: "
      liftIO $ print t
      let tT = checkTerm t
      case tT of
        (Left e, st, logs) -> do
          liftIO $ putStr "ERROR: " >> putStrLn (show e)
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
        (Right tT, st, logs) -> do
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty t, " :: ", pretty tT]
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
      let a = eval t ds
      let aT = checkTerm a
      case aT of
        (Left e, st, logs) -> do
          liftIO $ putStr "ERROR: " >> putStrLn (show e)
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)
        (Right aT, st, logs) -> do
          liftIO $ putStr "eval: "
          liftIO $ print a
          liftIO $ putStr "print: "
          liftIO $ putStrLn $ T.unpack $ T.concat [pretty a, " :: ", pretty aT]
          liftIO $ putStr "LOGS: "  >> putStrLn (show logs)

complete :: CompletionFunc (StateT FideST IO)
complete (ante, post)
  | prefixes [":q ", ":quit ", ":h ", ":help "] p = noCompletion (ante, post)
  | prefixes [":l ", ":load "] p = completeFilename (ante, post)
  | prefixes [":let "] p = do
     ns <- gets (M.keys . topDefs)
     let f word = T.unpack <$> filter (T.isPrefixOf (T.pack word)) ns
     completeWord Nothing " " (pure . (map simpleCompletion) . f)  (ante, post)
  | otherwise = do
     ns <- gets (M.keys . topDefs)
     let ks = [":quit", ":help", ":let", ":load"]
     let f word = T.unpack <$> filter (T.isPrefixOf (T.pack word)) (ks ++ ns)
     completeWord Nothing " " (pure . (map simpleCompletion) . f)  (ante, post)
  where
    p = reverse ante

prefixes :: [String] -> String -> Bool
prefixes (p:ps) x = isPrefixOf p x || prefixes ps x
prefixes [] x = False

fide :: StateT FideST IO ()
fide = repl prompt quit process complete ini
  where
    ini = liftIO $ putStrLn
      "Welcome to Fide, the Formality interactive development environment!"


