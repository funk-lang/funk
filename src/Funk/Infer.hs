{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Infer where

import Control.Monad.State
import Funk.Fresh
import Funk.STerm
import Funk.Term

data Constraint = CEq SType SType

constraints :: STerm -> Fresh [Constraint]
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

infer :: STerm -> IO [Constraint]
infer term = fst <$> runFresh (constraints term) emptyEnv
