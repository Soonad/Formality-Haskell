{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module HaskelineT where

import           Data.Text                  (Text)
import qualified Data.Text                  as T

import Data.List (isPrefixOf)
import Control.Applicative
import Control.Monad.Fail as Fail
import Control.Monad.State.Strict
import Control.Monad.Reader

import System.Console.Haskeline.Completion
import System.Console.Haskeline.MonadException
import qualified System.Console.Haskeline as H

newtype HaskelineT m a = HaskelineT { unHaskeline :: H.InputT m a }
 deriving (Monad, Functor, Applicative, MonadIO, MonadException, MonadTrans, MonadHaskeline)

-- | Run HaskelineT monad
runHaskelineT :: MonadException m => H.Settings m -> HaskelineT m a -> m a
runHaskelineT s m = H.runInputT s (H.withInterrupt (unHaskeline m))

class MonadException m => MonadHaskeline m where
  getInputLine :: Text -> m (Maybe Text)
  getInputChar :: Text -> m (Maybe Char)
  outputTxt    :: Text -> m ()
  outputTxtLn  :: Text -> m ()

instance MonadException m => MonadHaskeline (H.InputT m) where
  getInputLine t = (fmap T.pack) <$> H.getInputLine (T.unpack t)
  getInputChar = H.getInputChar . T.unpack
  outputTxt    = H.outputStr . T.unpack
  outputTxtLn  = H.outputStrLn . T.unpack

instance Fail.MonadFail m => Fail.MonadFail (HaskelineT m) where
  fail = lift . Fail.fail

instance MonadState s m => MonadState s (HaskelineT m) where
  get = lift get
  put = lift . put

instance MonadReader r m => MonadReader r (HaskelineT m) where
  ask                    = lift ask
  local f (HaskelineT m) = HaskelineT $ H.mapInputT (local f) m

instance (MonadHaskeline m) => MonadHaskeline (StateT s m) where
  getInputLine = lift . getInputLine
  getInputChar = lift . getInputChar
  outputTxt    = lift . outputTxt
  outputTxtLn  = lift . outputTxtLn

-- | Wrap a HasklineT action so that if an interrupt is thrown the shell continues as normal.
tryAction :: MonadException m => HaskelineT m a -> HaskelineT m a
tryAction (HaskelineT f) = HaskelineT (H.withInterrupt loop)
    where loop = handle (\H.Interrupt -> loop) f

-- | Catch all toplevel failures.
dontCrash :: (MonadIO m, H.MonadException m) => m () -> m ()
dontCrash m = H.catch m ( \ e@SomeException{} -> liftIO ( putStrLn ( show e ) ) )

-- | Abort the current REPL loop, and continue.
abort :: MonadIO m => HaskelineT m a
abort = throwIO H.Interrupt


