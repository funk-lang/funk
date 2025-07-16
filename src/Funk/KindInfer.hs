{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.KindInfer where

import Control.Monad.IO.Class
import Control.Monad.State
import Data.IORef
import Funk.Fresh
import Funk.STerm
import Funk.Term
import qualified Funk.Subst as S
import Text.Parsec (SourcePos)

data KindConstraint
  = KEq SKind SKind
  | KArrowConstraint SKind SKind SKind -- first -> second = third

-- Kind inference for types
kindInferType :: SType -> Fresh [KindConstraint]
kindInferType = \case
  TVar ref -> do
    -- Type variables have kind *
    pos <- liftIO $ bindingPos ref
    starKind <- freshStarKind pos
    return [KEq (KVar $ error "need kind var for type var") starKind]
  TArrow t1 t2 -> do
    cs1 <- kindInferType t1
    cs2 <- kindInferType t2
    pos <- liftIO $ typePos t1
    starKind1 <- freshStarKind pos
    starKind2 <- freshStarKind pos
    -- Both argument and result types must have kind *
    return $ cs1 ++ cs2 ++ [KEq (KVar $ error "need kind var") starKind1, KEq (KVar $ error "need kind var") starKind2]
  TForall _ t -> kindInferType t
  TApp t1 t2 -> do
    cs1 <- kindInferType t1
    cs2 <- kindInferType t2
    pos <- liftIO $ typePos t1
    k1 <- freshUnboundKind pos
    k2 <- freshUnboundKind pos
    resultKind <- freshUnboundKind pos
    -- t1 must have kind k2 -> resultKind, t2 must have kind k2
    return $ cs1 ++ cs2 ++ [KArrowConstraint k2 resultKind (KVar $ error "kind var for t1")]

freshStarKind :: SourcePos -> Fresh SKind
freshStarKind _ = return KStar

freshUnboundKind :: SourcePos -> Fresh SKind
freshUnboundKind pos = do
  env <- get
  let idx = envNextIdx env
  put env {envNextIdx = idx + 1}
  liftIO $ KVar <$> newIORef (KUnbound pos idx)

-- Kind constraint solving
solveKindConstraints :: [KindConstraint] -> IO (Either String ())
solveKindConstraints cs = do
  mapM_ solveKindConstraint cs
  return $ Right ()

solveKindConstraint :: KindConstraint -> IO ()
solveKindConstraint = \case
  KEq k1 k2 -> unifyKinds k1 k2
  KArrowConstraint k1 k2 k3 -> unifyKinds k3 (KArrow k1 k2)

unifyKinds :: SKind -> SKind -> IO ()
unifyKinds k1 k2 = case (k1, k2) of
  (KStar, KStar) -> return ()
  (KVar ref1, k) -> do
    binding <- readIORef ref1
    case binding of
      KUnbound _ _ -> writeIORef ref1 (KBound k)
      KBound k' -> unifyKinds k' k
      _ -> error "Kind unification error"
  (k, KVar ref2) -> do
    binding <- readIORef ref2
    case binding of
      KUnbound _ _ -> writeIORef ref2 (KBound k)
      KBound k' -> unifyKinds k k'
      _ -> error "Kind unification error"
  (KArrow k1a k1b, KArrow k2a k2b) -> do
    unifyKinds k1a k2a
    unifyKinds k1b k2b
  _ -> error "Kind unification error"