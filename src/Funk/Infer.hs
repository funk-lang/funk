{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Infer where

import Control.Monad.State
import Funk.Fresh
import Funk.STerm
import Funk.Term

data Constraint = CEq SType SType

constraintsExpr :: SExpr -> Fresh [Constraint]
constraintsExpr = \case
  Var _ _ -> return []
  App ty t1 t2 -> do
    cs1 <- constraintsExpr t1
    cs2 <- constraintsExpr t2
    return $
      [CEq (TVar (typeOf t1)) (TArrow (TVar (typeOf t2)) (TVar ty))]
        ++ cs1
        ++ cs2
  Lam (SLam iTy oTy) _ mty body -> do
    cs <- constraintsExpr body
    let cs' = case mty of
          Just ann -> CEq (TVar iTy) ann : cs
          Nothing -> cs
    return $ CEq (TVar oTy) (TArrow (TVar iTy) (TVar $ typeOf body)) : cs'
  TyApp ty body outTy -> do
    pos <- liftIO $ bindingPos ty
    csFun <- constraintsExpr body
    iTy <- freshUnboundTy pos
    return $ CEq (TVar (typeOf body)) (TForall iTy outTy) : csFun
  BlockExpr ty block -> do
    cs <- constraintsBlock block
    return $ CEq (TVar ty) (TVar $ typeOf (blockExpr block)) : cs
  RecordType ty _ fields -> do
    csFields <- concat <$> mapM (const $ return []) fields
    freshTy <- freshUnboundTy (error "Record type has no position")
    return $ CEq (TVar ty) (TVar freshTy) : csFields
  RecordCreation ty expr fields -> do
    csExpr <- constraintsExpr expr
    csFields <- concat <$> mapM (constraintsExpr . snd) fields
    freshTy <- freshUnboundTy (error "Record creation has no position")
    return $ CEq (TVar ty) (TVar freshTy) : csExpr ++ csFields

constraintsStmt :: SStmt -> Fresh [Constraint]
constraintsStmt (Let ty _ mty body) = do
  csBody <- constraintsExpr body
  let cs' = case mty of
        Just ann -> CEq (TVar ty) ann : csBody
        Nothing -> csBody
  return $ CEq (TVar ty) (TVar $ typeOf body) : cs'
constraintsStmt (Type _ _) = return []
constraintsStmt (Data _ _) = return []
constraintsStmt (DataForall _ _ _) = return []

constraintsBlock :: SBlock -> Fresh [Constraint]
constraintsBlock (Block stmts expr) = do
  csStmts <- concat <$> mapM constraintsStmt stmts
  csExpr <- constraintsExpr expr
  return $ csStmts ++ csExpr

infer :: SExpr -> IO [Constraint]
infer expr = fst <$> runFresh (constraintsExpr expr) emptyEnv
