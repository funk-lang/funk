{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Subst where

import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Parser
import Funk.STerm
import Funk.Term
import Funk.Token
import Text.Parsec

data Env = Env
  { envVars :: Map Ident SBinding,
    envTys :: Map Ident STBinding,
    envVarTypes :: Map Ident STBinding,
    envNextIdx :: Int
  }

emptyEnv :: Env
emptyEnv = Env {envVars = Map.empty, envTys = Map.empty, envVarTypes = Map.empty, envNextIdx = 0}

newtype Subst a = Subst {unSubst :: ExceptT [(Located Ident)] (StateT Env IO) a}
  deriving (Functor, Monad, MonadIO, MonadState Env, MonadError [(Located Ident)])

instance Applicative Subst where
  pure = Subst . pure
  Subst f <*> Subst x = Subst $ do
    f' <- catchError (Right <$> f) (return . Left)
    x' <- catchError (Right <$> x) (return . Left)
    case (f', x') of
      (Right fVal, Right xVal) -> return (fVal xVal)
      (Left errs1, Left errs2) -> throwError (errs1 ++ errs2)
      (Left errs, _) -> throwError errs
      (_, Left errs) -> throwError errs

runSubst :: Subst a -> IO (Either [(Located Ident)] a, Env)
runSubst solver = runStateT (runExceptT $ unSubst solver) emptyEnv

freshSkolem :: Located Ident -> Subst STBinding
freshSkolem i = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO . newIORef $ Skolem i idx
  put
    env
      { envTys = Map.insert (unLocated i) ref $ envTys env,
        envNextIdx = envNextIdx env + 1
      }
  return ref

freshUnboundTy :: SourcePos -> Subst STBinding
freshUnboundTy pos = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO $ newIORef (Unbound pos idx)
  put env {envNextIdx = envNextIdx env + 1}
  return ref

substTy :: PType -> Subst SType
substTy pty = case pty of
  TVar i -> do
    env <- get
    case Map.lookup (unLocated i) (envTys env) of
      Just ref -> return $ TVar ref
      Nothing -> throwError [i]
  TArrow t1 t2 -> TArrow <$> substTy t1 <*> substTy t2
  TForall i t -> do
    ref <- freshSkolem i
    st <- substTy t
    return $ TForall ref st

substTerm :: PTerm -> Subst STerm
substTerm pterm = case pterm of
  Var _ (PBinding i) -> do
    env <- get
    termBinding <- case Map.lookup (unLocated i) (envVars env) of
      Just ref -> return ref
      Nothing -> throwError [i]
    typeBinding <- case Map.lookup (unLocated i) (envVarTypes env) of
      Just ty -> return ty
      Nothing -> throwError [i]
    return $ Var typeBinding termBinding
  Lam pos (PBinding i) mty body -> do
    i' <- liftIO $ newIORef (VUnbound i)
    iTy <- freshUnboundTy pos
    modify $ \env ->
      env
        { envVars = Map.insert (unLocated i) (SBinding i') (envVars env),
          envVarTypes = Map.insert (unLocated i) iTy (envVarTypes env)
        }
    tyAnn <- case mty of
      Just ty -> Just <$> substTy ty
      Nothing -> return Nothing
    body' <- substTerm body
    oTy <- freshUnboundTy pos
    return $ Lam (SLam iTy oTy) (SBinding i') tyAnn body'
  App pos t1 t2 -> App <$> freshUnboundTy pos <*> substTerm t1 <*> substTerm t2
  TyLam pos i body -> do
    ty <- freshUnboundTy pos
    i' <- freshSkolem i
    body' <- substTerm body
    return $ TyLam ty i' body'
  TyApp pos t ty -> TyApp <$> freshUnboundTy pos <*> substTerm t <*> substTy ty

subst :: PTerm -> IO (Either [(Located Ident)] (STerm), Env)
subst = runSubst . substTerm
