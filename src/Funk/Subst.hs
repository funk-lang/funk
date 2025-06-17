{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Subst where

import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Parser
import Funk.Term
import Funk.Token

data TBinding = Bound (Type TBinding) | Unbound (Located Ident) Int | Free Int
  deriving (Show, Eq)

type STBinding = IORef TBinding

type SType = Type STBinding

data Var = VBound (Term TBinding) | VUnbound (Located Ident)

newtype SBinding = SBinding {unSBinding :: IORef Var}

instance Binding SBinding where
  type BTVar SBinding = STBinding
  type BVar SBinding = STBinding
  type BLam SBinding = STBinding
  type BApp SBinding = STBinding
  type BTyLam SBinding = STBinding
  type BTyApp SBinding = STBinding

type STerm = Term SBinding

data Env = Env
  { envVars :: Map Ident SBinding,
    envTys :: Map Ident STBinding,
    envNextIdx :: Int
  }

emptyEnv :: Env
emptyEnv = Env {envVars = Map.empty, envTys = Map.empty, envNextIdx = 0}

newtype Subst a = Subst {unSubst :: ExceptT [Located Ident] (StateT Env IO) a}
  deriving (Functor, Monad, MonadIO, MonadState Env, MonadError [Located Ident])

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

runSubst :: Subst a -> IO (Either [Located Ident] a)
runSubst solver = fst <$> runStateT (runExceptT $ unSubst solver) emptyEnv

freshTy :: Located Ident -> Subst STBinding
freshTy i = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO . newIORef $ Unbound i idx
  put
    env
      { envTys = Map.insert (unLocated i) ref $ envTys env,
        envNextIdx = envNextIdx env + 1
      }
  return ref

freshFreeTy :: Subst STBinding
freshFreeTy = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO $ newIORef (Free idx)
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
    ref <- freshTy i
    st <- substTy t
    return $ TForall ref st

substTerm :: PTerm -> Subst STerm
substTerm pterm = case pterm of
  Var _ (PBinding i) -> do
    t <- freshFreeTy
    env <- get
    case Map.lookup (unLocated i) (envVars env) of
      Just ref -> return $ Var t ref
      Nothing -> throwError [i]
  Lam _ (PBinding i) mty body -> do
    i' <- liftIO $ newIORef (VUnbound i)
    modify $ \env ->
      env {envVars = Map.insert (unLocated i) (SBinding i') (envVars env)}
    ty <- case mty of
      Just ty -> Just <$> substTy ty
      Nothing -> return Nothing
    body' <- substTerm body
    lamTy <- freshFreeTy
    return $ Lam lamTy (SBinding i') ty body'
  App _ t1 t2 -> App <$> freshFreeTy <*> substTerm t1 <*> substTerm t2
  TyLam _ i body -> do
    ty <- freshFreeTy
    i' <- freshTy i
    body' <- substTerm body
    return $ TyLam ty i' body'
  TyApp _ t ty -> TyApp <$> freshFreeTy <*> substTerm t <*> substTy ty

subst :: PTerm -> IO (Either [Located Ident] STerm)
subst = runSubst . substTerm
