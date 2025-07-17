{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Infer where

import Control.Monad.IO.Class
import Funk.Fresh
import Funk.STerm
import Funk.Term

data Constraint
  = CEq SType SType
  | CTrait STBinding [STBinding] SType -- trait constraint: trait_name type_vars target_type

-- Bidirectional constraint generation: propagate expected types downward
constraintsExprWithExpected :: SExpr -> SType -> Fresh [Constraint]
constraintsExprWithExpected expr expectedType = do
  -- Generate normal constraints
  normalConstraints <- constraintsExpr expr
  -- Add constraint connecting expression type to expected type
  let expectedConstraint = CEq (TVar (typeOf expr)) expectedType
  -- Generate additional bidirectional constraints based on expression structure
  bidirectionalConstraints <- generateBidirectionalConstraints expr expectedType
  return $ expectedConstraint : normalConstraints ++ bidirectionalConstraints

-- Generate additional constraints for bidirectional type inference
generateBidirectionalConstraints :: SExpr -> SType -> Fresh [Constraint]
generateBidirectionalConstraints expr expectedType = case expr of
  App _ t1 t2 -> do
    case t1 of
      -- Case 1: Direct trait method application: pure@target arg -> expectedType
      TraitMethod _ _ _ targetType _ -> do
        case expectedType of
          TApp constructor _ -> 
            -- Expected type is "Constructor Arg", so target should be "Constructor"
            return [CEq targetType constructor]
          TVar _ -> 
            -- Expected type is a variable - connect them
            return [CEq targetType expectedType]
          _ -> return []
      
      -- Case 2: Function application where function is another app
      -- This handles: void (pure@target arg) where we need to infer target from expected type
      App _ innerFunc _ -> case innerFunc of
        TraitMethod methodType _ _ targetType _ -> do
          -- This is void (pure@target arg) where expected result helps infer target
          -- Strategy: pure@target :: #Unit -> target #Unit
          -- And void :: target #Unit -> target #Unit (from void signature)
          -- So the inner expression (pure@target #Unit) should have the same type as expected
          case expectedType of
            TApp constructor _ -> do
              -- If expected is State #Unit, then target should be State
              -- Generate constraint: target = State
              -- DEBUG: This should generate CEq t57 State for our example
              return [CEq targetType constructor]
            _ -> do
              -- Fallback: connect the method result type with expected type
              -- This creates a constraint that the trait method result matches expected
              return [CEq (TVar methodType) expectedType]
        _ -> do
          -- Regular nested application - propagate constraints
          subConstraints1 <- generateBidirectionalConstraints t1 (TArrow (TVar (typeOf t2)) expectedType)
          subConstraints2 <- generateBidirectionalConstraints t2 (TVar (typeOf t2))
          return $ subConstraints1 ++ subConstraints2
      
      -- Case 3: Variable or other expression types
      _ -> do
        -- Regular function application - try to propagate types
        subConstraints1 <- generateBidirectionalConstraints t1 (TArrow (TVar (typeOf t2)) expectedType)
        subConstraints2 <- generateBidirectionalConstraints t2 (TVar (typeOf t2))
        return $ subConstraints1 ++ subConstraints2
  
  -- For other expression types, recursively search for trait methods
  _ -> extractTraitMethodConstraints expr expectedType

-- Extract constraints for any trait methods found in the expression tree
extractTraitMethodConstraints :: SExpr -> SType -> Fresh [Constraint]
extractTraitMethodConstraints expr expectedType = case expr of
  TraitMethod _ _ _ targetType _ -> 
    case expectedType of
      TApp constructor _ -> return [CEq targetType constructor]
      _ -> return []
  App _ t1 t2 -> do
    cs1 <- extractTraitMethodConstraints t1 expectedType
    cs2 <- extractTraitMethodConstraints t2 expectedType  
    return $ cs1 ++ cs2
  _ -> return []

constraintsExpr :: SExpr -> Fresh [Constraint]
constraintsExpr = \case
  Var _ _ -> return []
  App ty t1 t2 -> do
    cs1 <- constraintsExpr t1
    cs2 <- constraintsExpr t2
    -- Special case: if t1 is an application of a TraitMethod, connect the target type
    extraConstraints <- case t1 of
      App _ (TraitMethod _ _ _ targetType _) _ ->
        -- Connect the trait method's target type with the argument type
        return [CEq targetType (TVar (typeOf t2))]
      _ -> return []
    return $
      extraConstraints
        ++ [CEq (TVar (typeOf t1)) (TArrow (TVar (typeOf t2)) (TVar ty))]
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
  TraitMethod _ traitName typeArgs targetType _ -> do
    -- Generate constraint that the target type implements the trait
    -- Convert Type STBinding to STBinding for typeArgs
    typeArgsRefs <- mapM (\_ -> freshUnboundTy (error "trait method type arg")) typeArgs
    -- Always generate a constraint to test the system
    return [CTrait traitName typeArgsRefs targetType]
  PrimUnit ty -> do
    -- #unit has type #Unit
    return [CEq (TVar ty) TUnit]
  PrimNil ty elemTy -> do
    -- #nil[T] has type #List T
    return [CEq (TVar ty) (TList elemTy)]
  PrimCons ty elemTy headExpr tailExpr -> do
    -- #cons[T] head tail has type #List T
    -- head has type T, tail has type #List T
    csHead <- constraintsExpr headExpr
    csTail <- constraintsExpr tailExpr
    return $ [ CEq (TVar ty) (TList elemTy),
               CEq (TVar (typeOf headExpr)) elemTy,
               CEq (TVar (typeOf tailExpr)) (TList elemTy)
             ] ++ csHead ++ csTail
  PrimPrint ty expr -> do
    -- #print expr has type #IO #Unit
    csExpr <- constraintsExpr expr
    return $ [ CEq (TVar ty) (TIO TUnit) ] ++ csExpr

constraintsStmt :: SStmt -> Fresh [Constraint]
constraintsStmt (Let ty _ mty body) = do
  -- Use bidirectional constraint generation when we have explicit type annotation
  (csBody, additionalConstraints) <- case mty of
    Just ann -> do
      -- Use bidirectional constraint generation with expected type
      bidiConstraints <- constraintsExprWithExpected body ann
      return ([], bidiConstraints ++ [CEq (TVar ty) ann])
    Nothing -> do
      -- Use normal constraint generation
      normalConstraints <- constraintsExpr body
      return (normalConstraints, [])
  return $ CEq (TVar ty) (TVar $ typeOf body) : csBody ++ additionalConstraints
constraintsStmt (Type {}) = return []
constraintsStmt (Data {}) = return []
constraintsStmt (DataForall {}) = return []
constraintsStmt (Trait {}) = return []
constraintsStmt (TraitWithKinds {}) = return []
constraintsStmt (Impl _ _ _ methods) = do
  concat <$> mapM (constraintsExpr . snd) methods

constraintsBlock :: SBlock -> Fresh [Constraint]
constraintsBlock (Block stmts expr) = do
  csStmts <- concat <$> mapM constraintsStmt stmts
  csExpr <- constraintsExpr expr
  return $ csStmts ++ csExpr

infer :: SExpr -> IO [Constraint]
infer expr = fst <$> runFresh (constraintsExpr expr) emptyEnv
