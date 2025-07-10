{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Solver where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Funk.Infer (Constraint (..))
import Funk.STerm
import Funk.Term
import Funk.Token
import Text.Parsec

data Env = Env {envNextIdx :: Int}

emptyEnv :: Env
emptyEnv = Env {envNextIdx = 0}

data SError
  = InfiniteType (Either SourcePos (Located Ident))
  | UnificationError SType SType

newtype Solver a = Solver {unSolver :: ExceptT [SError] (StateT Env IO) a}
  deriving (Functor, Monad, MonadIO, MonadState Env, MonadError [SError])

instance Applicative Solver where
  pure = Solver . pure
  Solver f <*> Solver x = Solver $ do
    f' <- catchError (Right <$> f) (return . Left)
    x' <- catchError (Right <$> x) (return . Left)
    case (f', x') of
      (Right fVal, Right xVal) -> return (fVal xVal)
      (Left errs1, Left errs2) -> throwError (errs1 ++ errs2)
      (Left errs, _) -> throwError errs
      (_, Left errs) -> throwError errs

runSolver :: Solver a -> Env -> IO (Either [SError] a)
runSolver solver env = fst <$> runStateT (runExceptT $ unSolver solver) env

freshUnboundTy :: SourcePos -> Solver STBinding
freshUnboundTy pos = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO $ newIORef (Unbound pos idx)
  put env {envNextIdx = envNextIdx env + 1}
  return ref

prune :: SType -> Solver SType
prune ty@(TVar ref) = do
  b <- liftIO $ readIORef ref
  case b of
    Bound ty' -> do
      ty'' <- prune ty'
      liftIO $ writeIORef ref (Bound ty'')
      return ty''
    _ -> return ty
prune (TArrow t1 t2) = TArrow <$> prune t1 <*> prune t2
prune (TForall v t) = TForall v <$> prune t

unify :: SType -> SType -> Solver ()
unify t1 t2 = do
  ta <- prune t1
  tb <- prune t2
  pos <- liftIO $ typePos ta
  case (ta, tb) of
    (TVar v1, TVar v2) | v1 == v2 -> return ()
    (TForall v1 t1', TForall v2 t2') -> do
      fresh <- freshUnboundTy pos
      let t1Subst = substituteTypeVar v1 (TVar fresh) t1'
      let t2Subst = substituteTypeVar v2 (TVar fresh) t2'
      unify t1Subst t2Subst
    (TForall v t, other) -> do
      fresh <- freshUnboundTy pos
      let tSubst = substituteTypeVar v (TVar fresh) t
      unify tSubst other
    (other, TForall v t) -> do
      fresh <- freshUnboundTy pos
      let tSubst = substituteTypeVar v (TVar fresh) t
      unify other tSubst
    (TVar v1, TVar v2) -> do
      v1' <- liftIO $ readIORef v1
      v2' <- liftIO $ readIORef v2
      case (v1', v2') of
        (Skolem _ id1, Skolem _ id2) ->
          when (id1 /= id2) $ throwError [UnificationError ta tb]
        (Unbound _ id1, Unbound _ id2) ->
          if id1 < id2
            then bindVar v2 ta
            else bindVar v1 tb
        (Unbound {}, Skolem {}) -> bindVar v1 tb
        (Skolem {}, Unbound {}) -> bindVar v2 ta
        _ -> throwError [UnificationError ta tb]
    (TVar v, r) -> do
      v' <- liftIO $ readIORef v
      case v' of
        Skolem {} -> throwError [UnificationError (TVar v) r]
        Unbound {} -> bindVar v r
        _ -> throwError [UnificationError (TVar v) r]
    (l, TVar v) -> do
      v' <- liftIO $ readIORef v
      case v' of
        Skolem {} -> throwError [UnificationError l (TVar v)]
        Unbound {} -> bindVar v l
        _ -> throwError [UnificationError l (TVar v)]
    (TArrow a1 a2, TArrow b1 b2) -> unify a1 b1 >> unify a2 b2

substituteTypeVar :: STBinding -> SType -> SType -> SType
substituteTypeVar old new ty = case ty of
  TVar ref | ref == old -> new
  TVar ref -> TVar ref
  TArrow t1 t2 -> TArrow (substituteTypeVar old new t1) (substituteTypeVar old new t2)
  TForall v t | v == old -> TForall v t
  TForall v t -> TForall v (substituteTypeVar old new t)

bindVar :: STBinding -> SType -> Solver ()
bindVar v ty = do
  occurs <- occursCheck v ty
  when occurs $ do
    v' <- liftIO $ readIORef v
    case v' of
      Skolem i _ -> throwError [InfiniteType $ Right i]
      Unbound pos _ -> throwError [InfiniteType $ Left pos]
      _ -> return ()
  liftIO $ writeIORef v (Bound ty)

occursCheck :: STBinding -> SType -> Solver Bool
occursCheck v t = do
  t' <- prune t
  case t' of
    TVar v' -> return (v == v')
    TArrow x y -> (||) <$> occursCheck v x <*> occursCheck v y
    TForall _ th -> occursCheck v th

solve :: [Constraint] -> Solver ()
solve = mapM_ go
  where
    go (CEq t1 t2) = unify t1 t2

solveConstraints :: [Constraint] -> Env -> IO (Either [SError] ())
solveConstraints cs env = do
  res' <- runSolver (solve cs) env
  case res' of
    Left errs -> return (Left errs)
    Right () -> return (Right ())
