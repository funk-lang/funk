{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Funk.Subst where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Parser
import Funk.Term
import Funk.Token

data Binding = Bound (Type Binding) | Unbound (Located Ident) Int
  deriving (Show, Eq)

type SType = Type (IORef Binding)

data Var = VBound (Term Identity (IORef Binding) Var) | VUnbound (Located Ident)

type STerm = Term Identity (IORef Binding) (IORef Var)

data Env = Env
  { envVars :: Map Ident (IORef Var),
    envTys :: Map Ident (IORef Binding),
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

freshTy :: Located Ident -> Subst (IORef Binding)
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
  Var i -> do
    env <- get
    case Map.lookup (unLocated i) (envVars env) of
      Just ref -> return $ Var ref
      Nothing -> throwError [i]
  Lam i mty body -> do
    i' <- liftIO $ newIORef (VUnbound i)
    modify $ \env ->
      env {envVars = Map.insert (unLocated i) i' (envVars env)}
    ty <- case mty of
      Just ty -> substTy ty
      Nothing -> TVar <$> freshTy i
    body' <- substTerm body
    return $ Lam i' (pure ty) body'
  App t1 t2 -> App <$> substTerm t1 <*> substTerm t2
  TyLam i body -> do
    i' <- freshTy i
    body' <- substTerm body
    return $ TyLam i' body'
  TyApp t ty -> TyApp <$> substTerm t <*> substTy ty

subst :: PTerm -> IO (Either [Located Ident] STerm)
subst = runSubst . substTerm
