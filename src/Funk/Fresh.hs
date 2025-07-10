{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Fresh where

import Control.Monad.State
import Data.IORef
import Funk.STerm
import Text.Parsec

data Env = Env {envNextIdx :: Int}

emptyEnv :: Env
emptyEnv = Env {envNextIdx = 0}

newtype Fresh a = Fresh {unFresh :: (StateT Env IO) a}
  deriving (Functor, Applicative, Monad, MonadIO, MonadState Env)

runFresh :: Fresh a -> Env -> IO (a, Env)
runFresh solver env = runStateT (unFresh solver) env

freshUnboundTy :: SourcePos -> Fresh STBinding
freshUnboundTy pos = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO $ newIORef (Unbound pos idx)
  put env {envNextIdx = envNextIdx env + 1}
  return ref
