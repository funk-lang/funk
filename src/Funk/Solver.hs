{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Solver where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Funk.Infer (Constraint (..), InferResult (..), KindConstraint (..))
import Funk.STerm
import qualified Funk.Subst as S
import Funk.Term
import Funk.Token
import Text.Parsec

data SError
  = InfiniteType (Either SourcePos (Located Ident))
  | UnificationError SType SType
  | MissingTraitImpl SourcePos STBinding SType
  | KindUnificationError
  | KindArityMismatch
  | UnboundKindVariable
  | InvalidKindBinding

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
prune (TList t) = TList <$> prune t
prune TUnit = return TUnit
prune (TConstraint traitName typeVars targetType bodyType) = do
  targetType' <- prune targetType
  bodyType' <- prune bodyType
  return $ TConstraint traitName typeVars targetType' bodyType'

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
    (TApp a1 a2, TApp b1 b2) -> unify a1 b1 >> unify a2 b2
    (TList a, TList b) -> unify a b
    (TUnit, TUnit) -> return ()
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
    (TApp (TVar v) _arg, other) -> do
      v' <- liftIO $ readIORef v
      case v' of
        Unbound {} -> do
          freshArg <- freshUnboundTyS pos
          let functionType = TArrow (TVar freshArg) other
          bindVar v functionType
        _ -> throwError [UnificationError ta tb]
    (other, TApp (TVar v) _arg) -> do
      v' <- liftIO $ readIORef v
      case v' of
        Unbound {} -> do
          freshArg <- freshUnboundTyS pos
          let functionType = TArrow (TVar freshArg) other
          bindVar v functionType
        _ -> throwError [UnificationError ta tb]
    (TConstraint traitName typeVars targetType bodyType, other) -> do
      case typeVars of
        [] -> do
          solveTrait traitName [] targetType
          unify bodyType other
        (_firstVar:_restVars) -> do
          freshVars <- mapM (\_ -> freshUnboundTyS pos) typeVars
          case freshVars of
            [] -> throwError [UnificationError ta tb] -- This shouldn't happen since typeVars is non-empty
            (firstFresh:_) -> do
              let skolemizedTarget = foldr (\var acc -> substituteTypeVar var (TVar firstFresh) acc) targetType typeVars
              let skolemizedBody = foldr (\var acc -> substituteTypeVar var (TVar firstFresh) acc) bodyType typeVars
              solveTrait traitName freshVars skolemizedTarget
              unify skolemizedBody other
    (other, TConstraint traitName typeVars targetType bodyType) -> do
      case typeVars of
        [] -> do
          solveTrait traitName [] targetType
          unify other bodyType
        (_firstVar:_restVars) -> do
          freshVars <- mapM (\_ -> freshUnboundTyS pos) typeVars
          case freshVars of
            [] -> throwError [UnificationError ta tb] -- This shouldn't happen since typeVars is non-empty
            (firstFresh:_) -> do
              let skolemizedTarget = foldr (\var acc -> substituteTypeVar var (TVar firstFresh) acc) targetType typeVars
              let skolemizedBody = foldr (\var acc -> substituteTypeVar var (TVar firstFresh) acc) bodyType typeVars
              solveTrait traitName freshVars skolemizedTarget
              unify other skolemizedBody
    _ -> throwError [UnificationError ta tb]

substituteTypeVar :: STBinding -> SType -> SType -> SType
substituteTypeVar old new ty = case ty of
  TVar ref | ref == old -> new
  TVar ref -> TVar ref
  TArrow t1 t2 -> TArrow (substituteTypeVar old new t1) (substituteTypeVar old new t2)
  TForall v t | v == old -> TForall v t
  TForall v t -> TForall v (substituteTypeVar old new t)
  TConstraint traitName typeVars targetType bodyType ->
    TConstraint traitName typeVars (substituteTypeVar old new targetType) (substituteTypeVar old new bodyType)
  TApp t1 t2 -> TApp (substituteTypeVar old new t1) (substituteTypeVar old new t2)
  TList t -> TList (substituteTypeVar old new t)
  TUnit -> TUnit

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
    TConstraint _ _ targetType bodyType -> (||) <$> occursCheck v targetType <*> occursCheck v bodyType
    TApp t1 t2 -> (||) <$> occursCheck v t1 <*> occursCheck v t2
    TList t1 -> occursCheck v t1
    TUnit -> return False

solveTrait :: STBinding -> [STBinding] -> SType -> Solver ()
solveTrait traitName typeArgs targetType = do
  env <- get
  prunedTarget <- prune targetType
  maybeImpl <- findMatchingImpl traitName typeArgs prunedTarget (S.envImpls env)
  case maybeImpl of
    Just _impl -> return ()
    Nothing -> do
      pos <- liftIO $ typePos targetType
      throwError [MissingTraitImpl pos traitName targetType]

solve :: [Constraint] -> Solver ()
solve = mapM_ go
  where
    go (CEq t1 t2) = unify t1 t2
    go (CTrait traitName typeArgs targetType) = solveTrait traitName typeArgs targetType

traitsMatch :: STBinding -> STBinding -> Solver Bool
traitsMatch trait1 trait2 = do
  name1 <- liftIO $ sTBindingToIdent trait1
  name2 <- liftIO $ sTBindingToIdent trait2
  return (name1 == name2)

findMatchingImpl :: STBinding -> [STBinding] -> SType -> [(STBinding, [STBinding], SType, SStmt)] -> Solver (Maybe SStmt)
findMatchingImpl traitName _typeArgs targetType impls = do
  matches <- forM impls $ \(implTrait, _implVars, implType, impl) -> do
    traitMatch <- traitsMatch traitName implTrait
    if traitMatch
      then do
        typeMatch <- typesUnify targetType implType
        return $ if typeMatch then Just impl else Nothing
      else return Nothing
  return $ case concatMap maybeToList matches of
    (impl : _) -> Just impl
    [] -> Nothing
  where
    maybeToList Nothing = []
    maybeToList (Just x) = [x]

typesUnify :: SType -> SType -> Solver Bool
typesUnify t1 t2 = do
  env <- liftIO $ newIORef emptyUnificationEnv
  result <- liftIO $ tryUnify env t1 t2
  case result of
    Right () -> return True
    Left _ -> return False

newtype UnificationEnv = UnificationEnv {unifSubst :: [(STBinding, SType)]}

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
          modifyIORef envRef $ \env -> env {unifSubst = (v1, t) : unifSubst env}
          return $ Right ()
    (t, TVar v2) -> do
      occurs <- occursCheckIO v2 t
      if occurs
        then return $ Left "occurs check"
        else do
          modifyIORef envRef $ \env -> env {unifSubst = (v2, t) : unifSubst env}
          return $ Right ()
    (TConstraint _traitName1 _typeVars1 targetType1 bodyType1, TConstraint _traitName2 _typeVars2 targetType2 bodyType2) -> do
      r1 <- tryUnify envRef targetType1 targetType2
      case r1 of
        Left err -> return $ Left err
        Right () -> tryUnify envRef bodyType1 bodyType2
    (TConstraint _traitName _typeVars _targetType bodyType, other) -> do
      tryUnify envRef bodyType other
    (other, TConstraint _traitName _typeVars _targetType bodyType) -> do
      tryUnify envRef other bodyType
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
    (TList t1'', TList t2'') -> tryUnify envRef t1'' t2''
    (TUnit, TUnit) -> return $ Right ()
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
    TConstraint traitName typeVars targetType bodyType -> do
      targetType' <- substAndPrune envRef targetType
      bodyType' <- substAndPrune envRef bodyType
      return $ TConstraint traitName typeVars targetType' bodyType'
    TApp t1 t2 -> TApp <$> substAndPrune envRef t1 <*> substAndPrune envRef t2
    TArrow t1 t2 -> TArrow <$> substAndPrune envRef t1 <*> substAndPrune envRef t2
    TForall v t -> TForall v <$> substAndPrune envRef t
    TList t -> TList <$> substAndPrune envRef t
    TUnit -> return TUnit

occursCheckIO :: STBinding -> SType -> IO Bool
occursCheckIO var ty = case ty of
  TVar ref | ref == var -> return False
  TVar ref -> do
    binding <- readIORef ref
    case binding of
      Bound boundTy -> occursCheckIO var boundTy
      _ -> return False
  TConstraint _ _ targetType bodyType -> do
    r1 <- occursCheckIO var targetType
    if r1 then return True else occursCheckIO var bodyType
  TApp t1 t2 -> do
    r1 <- occursCheckIO var t1
    if r1 then return True else occursCheckIO var t2
  TArrow t1 t2 -> do
    r1 <- occursCheckIO var t1
    if r1 then return True else occursCheckIO var t2
  TForall v t -> if v == var then return False else occursCheckIO var t
  TList t -> occursCheckIO var t
  TUnit -> return False

solveConstraints :: InferResult -> S.Env -> IO (Either [SError] ())
solveConstraints result env = do
  res <- solveKindConstraints $ kindConstraints result
  case res of
    Left errs -> return $ Left errs
    Right () -> do
      res' <- runSolver (solve $ typeConstraints result) env
      case res' of
        Left errs -> return $ Left errs
        Right () -> return $ Right ()

solveTypeConstraints :: [Constraint] -> S.Env -> IO (Either [SError] ())
solveTypeConstraints cs env = do
  res' <- runSolver (solve cs) env
  case res' of
    Left errs -> return (Left errs)
    Right () -> return (Right ())

solveKindConstraints :: [KindConstraint] -> IO (Either [SError] ())
solveKindConstraints cs = do
  results <- mapM trySolveKindConstraint cs
  case sequence results of
    Left errs -> return $ Left errs
    Right _ -> return $ Right ()

trySolveKindConstraint :: KindConstraint -> IO (Either [SError] ())
trySolveKindConstraint constraint = do
  result <- tryIO $ solveKindConstraint constraint
  case result of
    Left err -> return $ Left [err]
    Right () -> return $ Right ()
  where
    tryIO action = do
      result <- action
      case result of
        Left err -> return $ Left err
        Right () -> return $ Right ()

solveKindConstraint :: KindConstraint -> IO (Either SError ())
solveKindConstraint = \case
  KEq k1 k2 -> unifyKinds k1 k2
  KArrowConstraint k1 k2 k3 -> unifyKinds k3 (KArrow k1 k2)

unifyKinds :: SKind -> SKind -> IO (Either SError ())
unifyKinds k1 k2 = case (k1, k2) of
  (KStar, KStar) -> return $ Right ()
  (KVar ref1, k) -> do
    binding <- readIORef ref1
    case binding of
      KUnbound _ _ -> do
        writeIORef ref1 (KBound k)
        return $ Right ()
      KBound k' -> unifyKinds k' k
      _ -> return $ Left InvalidKindBinding
  (k, KVar ref2) -> do
    binding <- readIORef ref2
    case binding of
      KUnbound _ _ -> do
        writeIORef ref2 (KBound k)
        return $ Right ()
      KBound k' -> unifyKinds k k'
      _ -> return $ Left InvalidKindBinding
  (KArrow k1a k1b, KArrow k2a k2b) -> do
    r1 <- unifyKinds k1a k2a
    case r1 of
      Left err -> return $ Left err
      Right () -> unifyKinds k1b k2b
  _ -> return $ Left KindUnificationError
