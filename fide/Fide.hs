module Fide where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.RWS.Lazy                  hiding (All)
import           Control.Monad.State.Strict
import           Control.Monad.Trans

import           Text.Megaparsec                         hiding (State)

import           Data.List                               (isPrefixOf)
import qualified Data.Map.Strict                         as M
import           Data.Maybe                              (isJust)
import           Data.Text                               (Text)
import qualified Data.Text                               as T

import           System.Process                          (callCommand)

import qualified System.Console.Haskeline                as H
import           System.Console.Haskeline.Completion
import           System.Console.Haskeline.MonadException

import           Check
import           Core                                    (ID(..), Module(..), Name,eval)
import qualified Core                                    as Core
import           CoreSyn                                 (runSyn, syn)
import qualified CoreSyn                                 as Syn
import           HaskelineT
import           Lang                                    (Parser, def, expr,
                                                          parseDefault, sc, sym)
import qualified Lang                                    as Lang
import           Pretty

data FideState = FideState
  { _fideModule :: Module
  , _idCount    :: ID
  }

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
  = Lets Name Lang.Term
  | Eval Lang.Term
  | Load FilePath
  | Quit
  | Help
  | Browse
  deriving (Eq, Show)

parseLine :: Lang.Parser Command
parseLine = sc >> line <* eof
  where 
    line = choice
      [ try $ (sym ":help" <|> sym ":h") >> return Help
      , try $ (sym ":quit" <|> sym ":q") >> return Quit
      , try $ do
          sym ":let";
          (n,t) <- sc >> def;
          optional (sym ";")
          return $ Lets n t
      , try $ do (sym ":load" <|> sym ":l")
                 (Load . T.unpack) <$> filename <* sc
      , try $ do (sym ":browse"); return Browse
      , try $ do
          (n,t) <- sc >> def;
          optional (sym ";")
          return $ Lets n t
      , Eval <$> Lang.expr
      ]

filename :: Parser Text
filename = takeWhile1P Nothing (\s -> s /= ' ')

process :: Text -> Repl ()
process line = do
  let res = parseDefault parseLine line
  either (\e -> liftIO $ print e) (\(c,_,_) -> procCommand c) res
  where
    procCommand :: Command -> Repl ()
    procCommand c = case c of
      Browse -> do
        ds <- gets $ _fideModule
        liftIO $ print ds
      Help   -> liftIO $ putStrLn "help text fills you with determination "
      Quit   -> abort
      Lets n t -> do
        i <- gets _idCount
        terms <- gets (Core._terms . _fideModule)
        names <- gets (Core._names . _fideModule)
        let names' = M.insert n i names
        let j = ID $ unID i + 1
        modify (\s -> s { _idCount = j })
        let env = Syn.SynEnv $ pure <$> names
        let ste = Syn.SynState j terms
        let (a,st,()) = runSyn env ste (syn t)
        case a of
          Left e  -> liftIO $ print e
          Right t -> do
            let i' = Syn._idCount st
            let modl' = Core.Module (M.insert i t (Syn._terms st)) names'
            put $ FideState modl' i'
      Eval t -> do
        i     <- gets _idCount
        terms <- gets (Core._terms . _fideModule)
        names <- gets (Core._names . _fideModule)
        let env = Syn.SynEnv $ pure <$> names
        let ste = Syn.SynState i terms
        let (a,st,()) = runSyn env ste (syn t)
        let modl = Module (Syn._terms st) names
        either (\e -> liftIO $ print e) (\t -> liftIO $ print $ eval t modl) a
        return ()

complete :: CompletionFunc (StateT FideState IO)
complete (ante, post)
  | prefixes [":q ", ":quit ", ":h ", ":help "] p = noCompletion (ante, post)
  | prefixes [":l ", ":load "] p = completeFilename (ante, post)
  | prefixes [":let "] p = do
     ns <- gets (M.keys . Core._names . _fideModule)
     let f word = T.unpack <$> filter (T.isPrefixOf (T.pack word)) ns
     completeWord Nothing " " (pure . (map simpleCompletion) . f)  (ante, post)
  | otherwise = do
     ns <- gets (M.keys . Core._names . _fideModule)
     let ks = [":quit", ":help", ":let", ":load"]
     let f word = T.unpack <$> filter (T.isPrefixOf (T.pack word)) (ks ++ ns)
     completeWord Nothing " " (pure . (map simpleCompletion) . f)  (ante, post)
  where
    p = reverse ante

prefixes :: [String] -> String -> Bool
prefixes (p:ps) x = isPrefixOf p x || prefixes ps x
prefixes [] x = False

fide :: StateT FideState IO ()
fide = repl prompt quit process complete ini
  where
    ini = liftIO $ putStrLn
      "Welcome to Fide, the Formality interactive development environment!"


