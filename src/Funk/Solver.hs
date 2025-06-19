{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Solver where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Parser
import Funk.Term
import Funk.Token
import Text.Parsec

data TBinding
  = Bound (Type STBinding)
  | Skolem (Located Ident) Int
  | Unbound SourcePos Int

showTBinding :: TBinding -> IO String
showTBinding (Bound ty) = showSType ty
showTBinding (Skolem i _) = return $ unIdent (unLocated i)
showTBinding (Unbound _ idx) = return $ "_" ++ show idx

type STBinding = IORef TBinding

bindingPos :: STBinding -> IO SourcePos
bindingPos ref = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

type SType = Type STBinding

showSType :: SType -> IO String
showSType (TVar ref) = do
  b <- readIORef ref
  showTBinding b
showSType (TArrow t1 t2) = do
  s1 <- showSType t1
  s2 <- showSType t2
  return $ "(" ++ s1 ++ " -> " ++ s2 ++ ")"
showSType (TForall ref t) = do
  b <- readIORef ref
  bStr <- showTBinding b
  st <- showSType t
  return $ "(\\/ " ++ bStr ++ " . " ++ st ++ ")"

typePos :: SType -> IO SourcePos
typePos (TVar ref) = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos
typePos (TArrow t1 _) = typePos t1
typePos (TForall ref _) = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

data Var = VBound STerm | VUnbound (Located Ident)

data SLam = SLam
  { sLamInput :: STBinding,
    sLamOutput :: STBinding
  }

newtype SBinding = SBinding {unSBinding :: IORef Var}

instance Binding SBinding where
  type BTVar SBinding = STBinding
  type BVar SBinding = STBinding
  type BLam SBinding = SLam
  type BApp SBinding = STBinding
  type BTyLam SBinding = STBinding
  type BTyApp SBinding = STBinding

type STerm = Term SBinding

showSTerm :: STerm -> IO String
showSTerm (Var _ ref) = do
  v <- readIORef (unSBinding ref)
  case v of
    VBound t -> showSTerm t
    VUnbound i -> return $ unIdent (unLocated i)
showSTerm (Lam ty ref _ body) = do
  v <- readIORef (unSBinding ref)
  bodyStr <- showSTerm body
  tyBinding <- readIORef $ sLamInput ty
  tyStr <- showTBinding tyBinding
  case v of
    VBound t -> do
      tStr <- showSTerm t
      return $ "(\\ " ++ tStr ++ " : " ++ tyStr ++ " . " ++ bodyStr ++ ")"
    VUnbound i ->
      return $ "(\\ " ++ unIdent (unLocated i) ++ " : " ++ tyStr ++ " . " ++ bodyStr ++ ")"
showSTerm (App _ t1 t2) = do
  s1 <- showSTerm t1
  s2 <- showSTerm t2
  return $ "(" ++ s1 ++ " " ++ s2 ++ ")"
showSTerm (TyLam _ ref body) = do
  b <- readIORef ref
  bStr <- showTBinding b
  bodyStr <- showSTerm body
  return $ "(/\\ " ++ bStr ++ " . " ++ bodyStr ++ ")"
showSTerm (TyApp _ t ty) = do
  s <- showSTerm t
  tyStr <- showSType ty
  return $ "(" ++ s ++ " [" ++ tyStr ++ "])"

data Env = Env
  { envVars :: Map Ident SBinding,
    envTys :: Map Ident STBinding,
    envVarTypes :: Map Ident STBinding,
    envNextIdx :: Int
  }

emptyEnv :: Env
emptyEnv = Env {envVars = Map.empty, envTys = Map.empty, envVarTypes = Map.empty, envNextIdx = 0}

data SError
  = MissingIdent (Located Ident)
  | InfiniteType (Either SourcePos (Located Ident))
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

runSolver :: Solver a -> IO (Either [SError] a)
runSolver solver = fst <$> runStateT (runExceptT $ unSolver solver) emptyEnv

freshSkolem :: Located Ident -> Solver STBinding
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

freshUnboundTy :: SourcePos -> Solver STBinding
freshUnboundTy pos = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO $ newIORef (Unbound pos idx)
  put env {envNextIdx = envNextIdx env + 1}
  return ref

substTy :: PType -> Solver SType
substTy pty = case pty of
  TVar i -> do
    env <- get
    case Map.lookup (unLocated i) (envTys env) of
      Just ref -> return $ TVar ref
      Nothing -> throwError [MissingIdent i]
  TArrow t1 t2 -> TArrow <$> substTy t1 <*> substTy t2
  TForall i t -> do
    ref <- freshSkolem i
    st <- substTy t
    return $ TForall ref st

substTerm :: PTerm -> Solver STerm
substTerm pterm = case pterm of
  Var _ (PBinding i) -> do
    env <- get
    termBinding <- case Map.lookup (unLocated i) (envVars env) of
      Just ref -> return ref
      Nothing -> throwError [MissingIdent i]
    typeBinding <- case Map.lookup (unLocated i) (envVarTypes env) of
      Just ty -> return ty
      Nothing -> throwError [MissingIdent i]
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

subst :: PTerm -> IO (Either [SError] STerm)
subst = runSolver . substTerm

data Constraint = CEq SType SType

typeOf :: STerm -> STBinding
typeOf = \case
  Var ty _ -> ty
  App ty _ _ -> ty
  Lam (SLam _ ty) _ _ _ -> ty
  TyLam ty _ _ -> ty
  TyApp ty _ _ -> ty

constraints :: STerm -> Solver [Constraint]
constraints = \case
  Var _ _ -> return []
  App ty t1 t2 -> do
    cs1 <- constraints t1
    cs2 <- constraints t2
    return $
      [CEq (TVar (typeOf t1)) (TArrow (TVar (typeOf t2)) (TVar ty))]
        ++ cs1
        ++ cs2
  Lam (SLam iTy oTy) _ mty body -> do
    cs <- constraints body
    let cs' = case mty of
          Just ann -> CEq (TVar iTy) ann : cs
          Nothing -> cs
    return $ CEq (TVar oTy) (TArrow (TVar iTy) (TVar $ typeOf body)) : cs'
  TyLam ty v body -> do
    cs <- constraints body
    return $ CEq (TVar ty) (TForall v (TVar (typeOf body))) : cs
  TyApp ty body outTy -> do
    pos <- liftIO $ bindingPos ty
    csFun <- constraints body
    iTy <- freshUnboundTy pos
    return $ CEq (TVar (typeOf body)) (TForall iTy outTy) : csFun

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

solve :: STerm -> Solver ()
solve t = do
  cs <- constraints t
  mapM_ go cs
  where
    go (CEq t1 t2) = unify t1 t2

solvePTerm :: PTerm -> IO (Either [SError] STerm)
solvePTerm pterm = do
  res <- subst pterm
  case res of
    Left errs -> return (Left errs)
    Right t -> do
      res' <- runSolver (solve t)
      case res' of
        Left errs -> return (Left errs)
        Right () -> return (Right t)
