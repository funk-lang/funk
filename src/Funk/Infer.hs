{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Infer
  ( Constraint (..),
    KindConstraint (..),
    infer,
    InferResult (..),
  )
where

import Control.Monad.IO.Class
import Control.Monad.State
import Data.IORef
import Funk.Fresh
import Funk.STerm
import Funk.Term
import Text.Parsec (SourcePos)

data Constraint
  = CEq SType SType
  | CTrait STBinding [STBinding] SType

data KindConstraint
  = KEq SKind SKind
  | KArrowConstraint SKind SKind SKind

data InferResult = InferResult
  { typeConstraints :: [Constraint],
    kindConstraints :: [KindConstraint]
  }

instance Semigroup InferResult where
  InferResult tc1 kc1 <> InferResult tc2 kc2 = InferResult (tc1 ++ tc2) (kc1 ++ kc2)

instance Monoid InferResult where
  mempty = InferResult [] []

constraintsExprWithExpected :: SExpr -> SType -> Fresh InferResult
constraintsExprWithExpected expr expectedType = do
  normalResult <- constraintsExpr expr
  let expectedConstraint = CEq (TVar (typeOf expr)) expectedType
  bidirectionalResult <- generateBidirectionalConstraints expr expectedType
  expectedKindConstraints <- kindInferType expectedType
  return $
    InferResult
      { typeConstraints = expectedConstraint : typeConstraints normalResult ++ typeConstraints bidirectionalResult,
        kindConstraints = kindConstraints normalResult ++ kindConstraints bidirectionalResult ++ expectedKindConstraints
      }

generateBidirectionalConstraints :: SExpr -> SType -> Fresh InferResult
generateBidirectionalConstraints expr expectedType = case expr of
  App _ t1 t2 -> do
    case t1 of
      TraitMethod _ _ _ targetType _ -> do
        typeConstraints' <- case expectedType of
          TApp constructor _ ->
            return [CEq targetType constructor]
          TVar _ ->
            return [CEq targetType expectedType]
          _ -> return []
        kindConstraints' <- kindInferType expectedType
        return $ InferResult typeConstraints' kindConstraints'
      App _ innerFunc _innerArg -> case innerFunc of
        TraitMethod methodType _ _ targetType _methodName -> do
          typeConstraints' <- case expectedType of
            TApp constructor _ -> do
              return [CEq targetType constructor]
            _ -> do
              return [CEq (TVar methodType) expectedType]
          kindConstraints' <- kindInferType expectedType
          return $ InferResult typeConstraints' kindConstraints'
        _ -> do
          subResult1 <- generateBidirectionalConstraints t1 (TArrow (TVar (typeOf t2)) expectedType)
          subResult2 <- generateBidirectionalConstraints t2 (TVar (typeOf t2))
          return $ subResult1 <> subResult2
      _ -> do
        subResult1 <- generateBidirectionalConstraints t1 (TArrow (TVar (typeOf t2)) expectedType)
        subResult2 <- generateBidirectionalConstraints t2 (TVar (typeOf t2))
        return $ subResult1 <> subResult2
  _ -> extractTraitMethodConstraints expr expectedType

extractTraitMethodConstraints :: SExpr -> SType -> Fresh InferResult
extractTraitMethodConstraints expr expectedType = case expr of
  TraitMethod _ _ _ targetType _ -> do
    typeConstraints' <- case expectedType of
      TApp constructor _ -> return [CEq targetType constructor]
      _ -> return []
    kindConstraints' <- kindInferType expectedType
    return $ InferResult typeConstraints' kindConstraints'
  App _ t1 t2 -> do
    result1 <- extractTraitMethodConstraints t1 expectedType
    result2 <- extractTraitMethodConstraints t2 expectedType
    return $ result1 <> result2
  _ -> return mempty

constraintsExpr :: SExpr -> Fresh InferResult
constraintsExpr = \case
  Var _ _ -> return mempty
  App ty t1 t2 -> do
    result1 <- constraintsExpr t1
    result2 <- constraintsExpr t2
    extraTypeConstraints <- case t1 of
      App _ (TraitMethod _ _ _ targetType _) _ ->
        return [CEq targetType (TVar (typeOf t2))]
      _ -> return []
    kindConstraints1 <- kindInferType (TVar (typeOf t1))
    kindConstraints2 <- kindInferType (TVar (typeOf t2))
    kindConstraints3 <- kindInferType (TVar ty)
    let baseTypeConstraints = [CEq (TVar (typeOf t1)) (TArrow (TVar (typeOf t2)) (TVar ty))]
    return $
      InferResult
        { typeConstraints = extraTypeConstraints ++ baseTypeConstraints ++ typeConstraints result1 ++ typeConstraints result2,
          kindConstraints = kindConstraints result1 ++ kindConstraints result2 ++ kindConstraints1 ++ kindConstraints2 ++ kindConstraints3
        }
  Lam (SLam iTy oTy) _ mty body -> do
    bodyResult <- constraintsExpr body
    let typeConstraints' = case mty of
          Just ann -> do
            annKindConstraints <- kindInferType ann
            return $
              InferResult
                { typeConstraints = [CEq (TVar iTy) ann, CEq (TVar oTy) (TArrow (TVar iTy) (TVar $ typeOf body))],
                  kindConstraints = kindConstraints bodyResult ++ annKindConstraints
                }
          Nothing -> do
            return $
              InferResult
                { typeConstraints = [CEq (TVar oTy) (TArrow (TVar iTy) (TVar $ typeOf body))],
                  kindConstraints = kindConstraints bodyResult
                }
    inputKindConstraints <- kindInferType (TVar iTy)
    outputKindConstraints <- kindInferType (TVar oTy)
    result <- typeConstraints'
    return $ result <> InferResult [] (inputKindConstraints ++ outputKindConstraints)
  TyApp ty body outTy -> do
    pos <- liftIO $ bindingPos ty
    bodyResult <- constraintsExpr body
    iTy <- freshUnboundTy pos
    bodyKindConstraints <- kindInferType (TVar (typeOf body))
    outKindConstraints <- kindInferType outTy
    tyKindConstraints <- kindInferType (TVar ty)
    return $
      InferResult
        { typeConstraints = [CEq (TVar (typeOf body)) (TForall iTy outTy)] ++ typeConstraints bodyResult,
          kindConstraints = kindConstraints bodyResult ++ bodyKindConstraints ++ outKindConstraints ++ tyKindConstraints
        }
  BlockExpr ty block -> do
    blockResult <- constraintsBlock block
    tyKindConstraints <- kindInferType (TVar ty)
    blockExprKindConstraints <- kindInferType (TVar $ typeOf (blockExpr block))
    return $
      InferResult
        { typeConstraints = [CEq (TVar ty) (TVar $ typeOf (blockExpr block))] ++ typeConstraints blockResult,
          kindConstraints = kindConstraints blockResult ++ tyKindConstraints ++ blockExprKindConstraints
        }
  RecordType ty _ _fields -> do
    freshTy <- freshUnboundTy (error "Record type has no position")
    tyKindConstraints <- kindInferType (TVar ty)
    freshKindConstraints <- kindInferType (TVar freshTy)
    return $
      InferResult
        { typeConstraints = [CEq (TVar ty) (TVar freshTy)],
          kindConstraints = tyKindConstraints ++ freshKindConstraints
        }
  RecordCreation ty expr _fields -> do
    exprResult <- constraintsExpr expr
    fieldsResults <- mapM (constraintsExpr . snd) _fields
    freshTy <- freshUnboundTy (error "Record creation has no position")
    tyKindConstraints <- kindInferType (TVar ty)
    freshKindConstraints <- kindInferType (TVar freshTy)
    let combinedFieldsResult = mconcat fieldsResults
    return $
      InferResult
        { typeConstraints = [CEq (TVar ty) (TVar freshTy)] ++ typeConstraints exprResult ++ typeConstraints combinedFieldsResult,
          kindConstraints = kindConstraints exprResult ++ kindConstraints combinedFieldsResult ++ tyKindConstraints ++ freshKindConstraints
        }
  TraitMethod _ traitName typeArgs targetType _ -> do
    typeArgsRefs <- mapM (\_ -> freshUnboundTy (error "trait method type arg")) typeArgs
    targetKindConstraints <- kindInferType targetType
    typeArgsKindConstraints <- concat <$> mapM (kindInferType . TVar) typeArgsRefs
    return $
      InferResult
        { typeConstraints = [CTrait traitName typeArgsRefs targetType],
          kindConstraints = targetKindConstraints ++ typeArgsKindConstraints
        }
  PrimUnit ty -> do
    tyKindConstraints <- kindInferType (TVar ty)
    unitKindConstraints <- kindInferType TUnit
    return $
      InferResult
        { typeConstraints = [CEq (TVar ty) TUnit],
          kindConstraints = tyKindConstraints ++ unitKindConstraints
        }
  PrimNil ty elemTy -> do
    tyKindConstraints <- kindInferType (TVar ty)
    listKindConstraints <- kindInferType (TList elemTy)
    elemKindConstraints <- kindInferType elemTy
    return $
      InferResult
        { typeConstraints = [CEq (TVar ty) (TList elemTy)],
          kindConstraints = tyKindConstraints ++ listKindConstraints ++ elemKindConstraints
        }
  PrimCons ty elemTy headExpr tailExpr -> do
    headResult <- constraintsExpr headExpr
    tailResult <- constraintsExpr tailExpr
    tyKindConstraints <- kindInferType (TVar ty)
    listKindConstraints <- kindInferType (TList elemTy)
    elemKindConstraints <- kindInferType elemTy
    headKindConstraints <- kindInferType (TVar (typeOf headExpr))
    tailKindConstraints <- kindInferType (TVar (typeOf tailExpr))
    return $
      InferResult
        { typeConstraints =
            [ CEq (TVar ty) (TList elemTy),
              CEq (TVar (typeOf headExpr)) elemTy,
              CEq (TVar (typeOf tailExpr)) (TList elemTy)
            ]
              ++ typeConstraints headResult
              ++ typeConstraints tailResult,
          kindConstraints =
            kindConstraints headResult
              ++ kindConstraints tailResult
              ++ tyKindConstraints
              ++ listKindConstraints
              ++ elemKindConstraints
              ++ headKindConstraints
              ++ tailKindConstraints
        }

constraintsStmt :: SStmt -> Fresh InferResult
constraintsStmt (Let ty _ mty body) = do
  (bodyResult, additionalResult) <- case mty of
    Just ann -> do
      bidiResult <- constraintsExprWithExpected body ann
      annKindConstraints <- kindInferType ann
      let additionalResult = InferResult [CEq (TVar ty) ann] annKindConstraints
      return (mempty, bidiResult <> additionalResult)
    Nothing -> do
      normalResult <- constraintsExpr body
      return (normalResult, mempty)

  tyKindConstraints <- kindInferType (TVar ty)
  bodyKindConstraints <- kindInferType (TVar $ typeOf body)

  let baseResult =
        InferResult
          { typeConstraints = [CEq (TVar ty) (TVar $ typeOf body)],
            kindConstraints = tyKindConstraints ++ bodyKindConstraints
          }

  return $ baseResult <> bodyResult <> additionalResult
constraintsStmt (Type {}) = return mempty
constraintsStmt (Data {}) = return mempty
constraintsStmt (DataForall {}) = return mempty
constraintsStmt (Trait {}) = return mempty
constraintsStmt (TraitWithKinds {}) = return mempty
constraintsStmt (Impl _ _ _ methods) = do
  results <- mapM (constraintsExpr . snd) methods
  return $ mconcat results

constraintsBlock :: SBlock -> Fresh InferResult
constraintsBlock (Block stmts expr) = do
  stmtResults <- mapM constraintsStmt stmts
  exprResult <- constraintsExpr expr
  return $ mconcat stmtResults <> exprResult

infer :: SBlock -> Env -> IO InferResult
infer expr env = fst <$> runFresh (constraintsBlock expr) env

kindInferType :: SType -> Fresh [KindConstraint]
kindInferType = \case
  TVar ref -> do
    pos <- liftIO $ bindingPos ref
    starKind <- freshStarKind pos
    kindVar <- getOrCreateKindVar ref
    return [KEq kindVar starKind]
  TArrow t1 t2 -> do
    cs1 <- kindInferType t1
    cs2 <- kindInferType t2
    pos <- liftIO $ typePos t1
    starKind1 <- freshStarKind pos
    starKind2 <- freshStarKind pos
    k1 <- getTypeKindVar t1
    k2 <- getTypeKindVar t2
    return $ cs1 ++ cs2 ++ [KEq k1 starKind1, KEq k2 starKind2]
  TForall _ t -> kindInferType t
  TApp t1 t2 -> do
    cs1 <- kindInferType t1
    cs2 <- kindInferType t2
    pos <- liftIO $ typePos t1
    k2 <- freshUnboundKind pos
    resultKind <- freshUnboundKind pos
    k1 <- getTypeKindVar t1
    k2Var <- getTypeKindVar t2
    return $ cs1 ++ cs2 ++ [KArrowConstraint k2 resultKind k1, KEq k2Var k2]
  TList t -> do
    cs <- kindInferType t
    pos <- liftIO $ typePos t
    starKind <- freshStarKind pos
    elemKindVar <- getTypeKindVar t
    return $ cs ++ [KEq elemKindVar starKind]
  TUnit -> do
    return []
  TConstraint _ _ _ t -> do
    kindInferType t

getOrCreateKindVar :: IORef TBinding -> Fresh SKind
getOrCreateKindVar ref = do
  pos <- liftIO $ bindingPos ref
  freshUnboundKind pos

getTypeKindVar :: SType -> Fresh SKind
getTypeKindVar t = do
  pos <- liftIO $ typePos t
  freshUnboundKind pos

freshStarKind :: SourcePos -> Fresh SKind
freshStarKind _ = return KStar

freshUnboundKind :: SourcePos -> Fresh SKind
freshUnboundKind pos = do
  env <- get
  let idx = envNextIdx env
  put env {envNextIdx = idx + 1}
  liftIO $ KVar <$> newIORef (KUnbound pos idx)
