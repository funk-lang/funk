{-# LANGUAGE LambdaCase #-}

module Funk.TypeChecker where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Funk.Term
import Funk.Token (Located (..))
import Text.Parsec.Pos (initialPos)

data TypeError
  = UnboundTermVar (Located Ident)
  | Mismatch Type Type
  | NotAFunction Type
  | NotForall Type
  deriving (Show, Eq)

data TypeEnv = TypeEnv
  { termEnv :: Map Ident Type,
    typeEnv :: Set Ident
  }

emptyEnv :: TypeEnv
emptyEnv = TypeEnv Map.empty Set.empty

type Subst = Map Ident Type

data TypeCheckerState = TypeCheckerState
  { count :: Int,
    subst :: Subst
  }

initialState :: TypeCheckerState
initialState = TypeCheckerState 0 Map.empty

type TypeChecker = ReaderT TypeEnv (StateT TypeCheckerState (Except TypeError))

runTypeChecker :: TypeEnv -> TypeChecker Type -> Either TypeError Type
runTypeChecker env m = runExcept $ evalStateT (runReaderT m env) initialState

freshTVar :: TypeChecker Type
freshTVar = do
  st <- get
  let n = count st
      v = Ident ("t" ++ show n)
      pos = initialPos "<fresh>"
  put st {count = n + 1}
  return $ TVar (Located pos v)

applySubst :: Type -> TypeChecker Type
applySubst = \case
  TVar (Located p a) -> do
    s <- gets subst
    case Map.lookup a s of
      Just t -> applySubst t
      Nothing -> return (TVar (Located p a))
  TArrow t1 t2 -> TArrow <$> applySubst t1 <*> applySubst t2
  TForall a t -> TForall a <$> applySubst t

extendSubst :: Ident -> Type -> TypeChecker ()
extendSubst a t = modify $ \st -> st {subst = Map.insert a t (subst st)}

unify :: Type -> Type -> TypeChecker ()
unify t1 t2 = do
  t1' <- applySubst t1
  t2' <- applySubst t2
  case (t1', t2') of
    (TVar (Located _ a), TVar (Located _ b)) | a == b -> return ()
    (TVar (Located _ a), ty) -> extendSubst a ty
    (ty, TVar (Located _ b)) -> extendSubst b ty
    (TArrow l1 r1, TArrow l2 r2) -> unify l1 l2 >> unify r1 r2
    (TForall a1 t1'', TForall a2 t2'') -> do
      alpha <- freshTVar
      let t1Renamed = substituteType a1 alpha t1''
      let t2Renamed = substituteType a2 alpha t2''
      unify t1Renamed t2Renamed
    (TForall {}, _) -> throwError $ Mismatch t1' t2'
    (_, TForall {}) -> throwError $ Mismatch t1' t2'

infer :: Term -> TypeChecker Type
infer = \case
  Var x -> do
    env <- asks termEnv
    case Map.lookup (unLocated x) env of
      Just ty -> return ty
      Nothing -> throwError $ UnboundTermVar x
  Lam x mAnn body -> do
    argTy <- maybe freshTVar return mAnn
    retTy <-
      local
        (\e -> e {termEnv = Map.insert (unLocated x) argTy (termEnv e)})
        (infer body)
    return $ TArrow argTy retTy
  App f e -> do
    tf <- infer f
    te <- infer e
    tv <- freshTVar
    unify tf (TArrow te tv)
    applySubst tv
  TyLam a body -> local (\e -> e {typeEnv = Set.insert (unLocated a) (typeEnv e)}) $ do
    t <- infer body
    return $ TForall a t
  TyApp t tyArg -> do
    t' <- infer t
    case t' of
      TForall a body -> return $ substituteType a tyArg body
      _ -> throwError $ NotForall t'

typeOf :: Term -> Either TypeError Type
typeOf = runTypeChecker emptyEnv . infer

substituteType :: Located Ident -> Type -> Type -> Type
substituteType (Located _ a) ty = go
  where
    go = \case
      TVar v@(Located _ x)
        | x == a -> ty
        | otherwise -> TVar v
      TArrow t1 t2 -> TArrow (go t1) (go t2)
      TForall v@(Located _ x) body
        | x == a -> TForall v body
        | otherwise -> TForall v (go body)
