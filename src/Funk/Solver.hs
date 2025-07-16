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
import qualified Funk.Subst as S
import Funk.Term
import Funk.Token
import System.IO.Unsafe
import Text.Parsec

data SError
  = InfiniteType (Either SourcePos (Located Ident))
  | UnificationError SType SType
  | MissingTraitImpl SourcePos STBinding SType

newtype Solver a = Solver {unSolver :: ExceptT [SError] (StateT S.Env IO) a}
  deriving (Functor, Applicative, Monad, MonadIO, MonadState S.Env, MonadError [SError])

runSolver :: Solver a -> S.Env -> IO (Either [SError] a)
runSolver solver env = fst <$> runStateT (runExceptT $ unSolver solver) env

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
prune (TApp t1 t2) = TApp <$> prune t1 <*> prune t2

freshUnboundTyS :: SourcePos -> Solver STBinding
freshUnboundTyS pos = do
  env <- get
  let idx = S.envNextIdx env
  put env {S.envNextIdx = idx + 1}
  liftIO $ newIORef (Unbound pos idx)

unify :: SType -> SType -> Solver ()
unify t1 t2 = do
  ta <- prune t1
  tb <- prune t2
  pos <- liftIO $ typePos ta
  case (ta, tb) of
    (TVar v1, TVar v2) | v1 == v2 -> return ()
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
    (TForall v1 t1', TForall v2 t2') -> do
      fresh <- freshUnboundTyS pos
      let t1Subst = substituteTypeVar v1 (TVar fresh) t1'
      let t2Subst = substituteTypeVar v2 (TVar fresh) t2'
      unify t1Subst t2Subst
    (TForall v t, other) -> do
      fresh <- freshUnboundTyS pos
      let tSubst = substituteTypeVar v (TVar fresh) t
      unify tSubst other
    (other, TForall v t) -> do
      fresh <- freshUnboundTyS pos
      let tSubst = substituteTypeVar v (TVar fresh) t
      unify other tSubst
    _ -> throwError [UnificationError ta tb]

substituteTypeVar :: STBinding -> SType -> SType -> SType
substituteTypeVar old new ty = case ty of
  TVar ref | ref == old -> new
  TVar ref -> TVar ref
  TArrow t1 t2 -> TArrow (substituteTypeVar old new t1) (substituteTypeVar old new t2)
  TForall v t | v == old -> TForall v t
  TForall v t -> TForall v (substituteTypeVar old new t)
  TApp t1 t2 -> TApp (substituteTypeVar old new t1) (substituteTypeVar old new t2)

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
    TForall v' th -> if v == v' then return False else occursCheck v th
    TApp t1 t2 -> (||) <$> occursCheck v t1 <*> occursCheck v t2

solve :: [Constraint] -> Solver ()
solve = mapM_ go
  where
    go (CEq t1 t2) = unify t1 t2
    go (CTrait traitName typeArgs targetType) = solveTrait traitName typeArgs targetType

solveTrait :: STBinding -> [STBinding] -> SType -> Solver ()
solveTrait traitName typeArgs targetType = do
  env <- get
  -- Prune the target type to get its canonical form
  prunedTarget <- prune targetType

  -- Look for matching implementation in envImpls
  case findMatchingImpl traitName typeArgs prunedTarget (S.envImpls env) of
    Just _impl -> return () -- Implementation found, constraint satisfied
    Nothing -> do
      pos <- liftIO $ typePos targetType
      throwError [MissingTraitImpl pos traitName targetType]

-- Check if two traits match by comparing their names
traitsMatch :: STBinding -> STBinding -> IO Bool
traitsMatch trait1 trait2 = do
  name1 <- sTBindingToIdent trait1
  name2 <- sTBindingToIdent trait2
  return (name1 == name2)

-- Find a matching trait implementation
findMatchingImpl :: STBinding -> [STBinding] -> SType -> [(STBinding, [STBinding], SType, SStmt)] -> Maybe SStmt
findMatchingImpl traitName _typeArgs targetType impls =
  case [ impl | (implTrait, _implVars, implType, impl) <- impls, let traitMatch = unsafePerformIO $ traitsMatch traitName implTrait, let typeMatch = unsafePerformIO $ typesUnify targetType implType, traitMatch && typeMatch
       ] of
    (impl : _) -> Just impl
    [] -> Nothing

-- Check if two types can unify (proper System FC unification)
typesUnify :: SType -> SType -> IO Bool
typesUnify t1 t2 = do
  env <- newIORef emptyUnificationEnv
  result <- tryUnify env t1 t2
  case result of
    Right () -> return True
    Left _ -> return False

data UnificationEnv = UnificationEnv { unifSubst :: [(STBinding, SType)] }

emptyUnificationEnv :: UnificationEnv
emptyUnificationEnv = UnificationEnv []

tryUnify :: IORef UnificationEnv -> SType -> SType -> IO (Either String ())
tryUnify envRef t1 t2 = do
  t1' <- substAndPrune envRef t1
  t2' <- substAndPrune envRef t2
  case (t1', t2') of
    (TVar v1, TVar v2) | v1 == v2 -> return $ Right ()
    (TVar v1, t) -> do
      occurs <- occursCheckIO v1 t
      if occurs 
        then return $ Left "occurs check"
        else do
          modifyIORef envRef $ \env -> env { unifSubst = (v1, t) : unifSubst env }
          return $ Right ()
    (t, TVar v2) -> do
      occurs <- occursCheckIO v2 t
      if occurs
        then return $ Left "occurs check"
        else do
          modifyIORef envRef $ \env -> env { unifSubst = (v2, t) : unifSubst env }
          return $ Right ()
    (TApp t1a t1b, TApp t2a t2b) -> do
      r1 <- tryUnify envRef t1a t2a
      case r1 of
        Left err -> return $ Left err
        Right () -> tryUnify envRef t1b t2b
    (TArrow t1a t1b, TArrow t2a t2b) -> do
      r1 <- tryUnify envRef t1a t2a
      case r1 of
        Left err -> return $ Left err
        Right () -> tryUnify envRef t1b t2b
    _ -> return $ Left "type mismatch"

substAndPrune :: IORef UnificationEnv -> SType -> IO SType
substAndPrune envRef ty = do
  env <- readIORef envRef
  case ty of
    TVar ref -> do
      case lookup ref (unifSubst env) of
        Just substTy -> substAndPrune envRef substTy
        Nothing -> do
          binding <- readIORef ref
          case binding of
            Bound boundTy -> substAndPrune envRef boundTy
            _ -> return ty
    TApp t1 t2 -> TApp <$> substAndPrune envRef t1 <*> substAndPrune envRef t2
    TArrow t1 t2 -> TArrow <$> substAndPrune envRef t1 <*> substAndPrune envRef t2
    TForall v t -> TForall v <$> substAndPrune envRef t

occursCheckIO :: STBinding -> SType -> IO Bool
occursCheckIO var ty = case ty of
  TVar ref | ref == var -> return False -- Same variable is fine for unification
  TVar ref -> do
    binding <- readIORef ref
    case binding of
      Bound boundTy -> occursCheckIO var boundTy
      _ -> return False
  TApp t1 t2 -> do
    r1 <- occursCheckIO var t1
    if r1 then return True else occursCheckIO var t2
  TArrow t1 t2 -> do
    r1 <- occursCheckIO var t1
    if r1 then return True else occursCheckIO var t2
  TForall v t -> if v == var then return False else occursCheckIO var t

solveConstraints :: [Constraint] -> S.Env -> IO (Either [SError] ())
solveConstraints cs env = do
  res' <- runSolver (solve cs) env
  case res' of
    Left errs -> return (Left errs)
    Right () -> return (Right ())
