{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.STerm where

import Control.Monad (forM)
import Data.IORef
import Funk.Term
import Funk.Token
import Text.Parsec
import qualified Text.Parsec.Pos as Pos

data TBinding
  = Bound (Type STBinding)
  | Skolem (Located Ident) Int
  | Unbound SourcePos Int

data KBinding
  = KBound (Kind SKBinding)
  | KSkolem (Located Ident) Int
  | KUnbound SourcePos Int

type STBinding = IORef TBinding
type SKBinding = IORef KBinding

bindingPos :: STBinding -> IO SourcePos
bindingPos ref = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

type SType = Type STBinding
type SKind = Kind SKBinding

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
typePos (TConstraint _ _ targetType _) = typePos targetType
typePos (TApp t1 _) = typePos t1
typePos (TList t) = typePos t
typePos TUnit = return (Pos.newPos "" 1 1)


data Var = VBound SExpr | VUnbound (Located Ident)

data SLam = SLam
  { sLamInput :: STBinding,
    sLamOutput :: STBinding
  }

newtype SBinding = SBinding {unSBinding :: IORef Var}

sTBindingToIdent :: STBinding -> IO Ident
sTBindingToIdent ref = do
  b <- readIORef ref
  case b of
    Skolem i _ -> return $ unLocated i
    _ -> return $ Ident "_"

sTBindingToIdentImproved :: STBinding -> IO Ident
sTBindingToIdentImproved ref = do
  b <- readIORef ref
  case b of
    Skolem i _ -> return $ unLocated i
    Unbound _ idx -> return $ Ident ("t" ++ show idx)
    Bound _ -> return $ Ident "_"  -- This shouldn't happen in this context

sBindingToIdent :: SBinding -> IO Ident
sBindingToIdent (SBinding ref) = do
  b <- readIORef ref
  case b of
    VBound _ -> return $ Ident "_"
    VUnbound i -> return $ unLocated i

-- Try to resolve trait method target types more intelligently
smartResolveTargetType :: SType -> STBinding -> IO (Type Ident)
smartResolveTargetType targetType exprType = do
  -- First try normal resolution
  normalResult <- sTypeToDisplay targetType
  
  case normalResult of
    TVar (Ident tname) | take 1 tname == "t" -> do
      -- This is still an unresolved type variable, try to infer from expression type
      exprTypeResolved <- sTypeToDisplay (TVar exprType)
      case exprTypeResolved of
        -- If the expression type is a concrete application like "State #Unit",
        -- extract the constructor "State" as the target type
        TApp (TVar constructor) _ -> return $ TVar constructor
        TVar constructor -> return $ TVar constructor
        _ -> return normalResult
    _ -> return normalResult

-- Enhanced type resolution that tries harder to resolve type variables
aggressiveTypeResolve :: SType -> IO (Type Ident)
aggressiveTypeResolve stype = do
  result <- sTypeToDisplay stype
  case result of
    TVar (Ident tname) | take 1 tname == "t" -> do
      -- Try to see if this type variable is actually bound to something concrete
      -- by following the binding chain more aggressively
      case stype of
        TVar ref -> do
          binding <- readIORef ref
          case binding of
            Bound boundType -> aggressiveTypeResolve boundType
            _ -> return result
        _ -> return result
    _ -> return result

-- Post-processing step to resolve trait method target types based on context
-- This is called after constraint solving to clean up unresolved trait method targets
resolveTraitMethodTargets :: SExpr -> IO (Expr Ident)
resolveTraitMethodTargets sexpr = do
  -- First convert normally
  normalExpr <- sExprToDisplayWithTypes sexpr
  -- Then apply context-based resolution
  contextResolveExpr normalExpr (typeOf sexpr)

-- Targeted resolution using explicit type annotation from let bindings
resolveTraitMethodsWithType :: SExpr -> Type Ident -> IO (Expr Ident)
resolveTraitMethodsWithType sexpr expectedType = do
  -- First convert normally
  normalExpr <- sExprToDisplayWithTypes sexpr
  -- Then apply direct resolution using the known expected type
  directResolveWithType normalExpr expectedType

-- Direct resolution that replaces trait method targets using expected type
directResolveWithType :: Expr Ident -> Type Ident -> IO (Expr Ident)
directResolveWithType expr expectedType = case expr of
  App _ f arg -> do
    f' <- directResolveWithType f expectedType
    arg' <- directResolveWithType arg expectedType
    return $ App () f' arg'
  
  TraitMethod _ traitName typeArgs (TVar (Ident tname)) methodName 
    | take 1 tname == "t" -> do
      -- This is an unresolved trait method target - use expected type to resolve it
      case expectedType of
        TApp constructor _ -> 
          -- If expected type is "Constructor Arg", target should be "Constructor"
          return $ TraitMethod () traitName typeArgs constructor methodName
        _ -> return expr
  
  _ -> return expr

-- Context-based resolution that looks at expression types to infer trait method targets
contextResolveExpr :: Expr Ident -> STBinding -> IO (Expr Ident)
contextResolveExpr expr exprType = case expr of
  App _ f arg -> do
    -- For function applications, we need to look at the overall result type
    exprTypeResolved <- sTypeToDisplay (TVar exprType)
    f' <- case f of
      TraitMethod _ traitName typeArgs (TVar (Ident tname)) methodName 
        | take 1 tname == "t" -> do
          -- This trait method application should produce the result type
          -- If result type is State #Unit, and this is pure@target #Unit, then target = State
          case exprTypeResolved of
            TApp constructor _ -> 
              return $ TraitMethod () traitName typeArgs constructor methodName
            _ -> return f
      _ -> contextResolveExpr f exprType
    return $ App () f' arg
  
  TraitMethod _ traitName typeArgs (TVar (Ident tname)) methodName 
    | take 1 tname == "t" -> do
      -- This is an unresolved trait method target - try to infer from context
      exprTypeResolved <- sTypeToDisplay (TVar exprType)
      case exprTypeResolved of
        TApp constructor _ -> 
          -- If the expression has type "Constructor Arg", target should be "Constructor"
          return $ TraitMethod () traitName typeArgs constructor methodName
        _ -> return expr
  
  _ -> return expr

instance Binding SBinding where
  type BTVar SBinding = STBinding
  type BVar SBinding = STBinding
  type BLam SBinding = SLam
  type BApp SBinding = STBinding
  type BTyApp SBinding = STBinding
  type BLet SBinding = STBinding
  type BBlock SBinding = STBinding
  type BRecord SBinding = STBinding
  type BRecordCreation SBinding = STBinding

type SExpr = Expr SBinding

type SStmt = Stmt SBinding

type SBlock = Block SBinding

blockExpr :: SBlock -> SExpr
blockExpr (Block _ e) = e

typeOf :: SExpr -> STBinding
typeOf = \case
  Var ty _ -> ty
  App ty _ _ -> ty
  Lam (SLam _ ty) _ _ _ -> ty
  TyApp ty _ _ -> ty
  BlockExpr ty _ -> ty
  RecordType ty _ _ -> ty
  RecordCreation ty _ _ -> ty
  TraitMethod ty _ _ _ _ -> ty
  PrimUnit ty -> ty
  PrimNil ty _ -> ty
  PrimCons ty _ _ _ -> ty

-- Enhanced version that includes type information for display
sExprToDisplayWithTypes :: SExpr -> IO (Expr Ident)
sExprToDisplayWithTypes sexpr = case sexpr of
  Var _ binding -> do
    binding' <- sBindingToIdent binding
    -- For variables, we'll add the type as a synthetic lambda annotation
    _ <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ Var () binding'
  App _ t1 t2 -> do
    t1' <- sExprToDisplayWithTypes t1
    t2' <- sExprToDisplayWithTypes t2
    return $ App () t1' t2'
  Lam _ binding mty body -> do
    binding' <- sBindingToIdent binding
    -- Extract the actual inferred type
    _ <- sTypeToDisplay (TVar (typeOf sexpr))
    mty' <- case mty of
      Just ty -> Just <$> sTypeToDisplay ty
      Nothing -> Just <$> sTypeToDisplay (TVar (typeOf sexpr)) -- Include inferred type
    body' <- sExprToDisplayWithTypes body
    return $ Lam () binding' mty' body'
  TyApp _ body outTy -> do
    body' <- sExprToDisplayWithTypes body
    outTy' <- sTypeToDisplay outTy
    return $ TyApp () body' outTy'
  BlockExpr _ block -> do
    block' <- sBlockToDisplayWithTypes block
    return $ BlockExpr () block'
  RecordType _ v fields -> do
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    v' <- sBindingToIdent v
    return $ RecordType () v' fields'
  RecordCreation _ expr fields -> do
    expr' <- sExprToDisplayWithTypes expr
    fields' <- forM fields $ \(f, e) -> do
      e' <- sExprToDisplayWithTypes e
      return (f, e')
    return $ RecordCreation () expr' fields'
  TraitMethod _ traitName typeArgs targetType methodName -> do
    traitName' <- sTBindingToIdent traitName
    typeArgs' <- mapM sTypeToDisplay typeArgs
    -- Try to resolve the target type more aggressively
    targetType' <- aggressiveTypeResolve targetType
    return $ TraitMethod () traitName' typeArgs' targetType' methodName
  PrimUnit _ -> return $ PrimUnit ()
  PrimNil _ ty -> do
    ty' <- sTypeToDisplay ty
    return $ PrimNil () ty'
  PrimCons _ ty headExpr tailExpr -> do
    ty' <- sTypeToDisplay ty
    head' <- sExprToDisplayWithTypes headExpr
    tail' <- sExprToDisplayWithTypes tailExpr
    return $ PrimCons () ty' head' tail'

-- Original version for backward compatibility
sExprToDisplay :: SExpr -> IO (Expr Ident)
sExprToDisplay = sExprToDisplayWithTypes


sTypeToDisplay :: SType -> IO (Type Ident)
sTypeToDisplay = sTypeToDisplayHelper []
  where
    sTypeToDisplayHelper :: [STBinding] -> SType -> IO (Type Ident)
    sTypeToDisplayHelper visited ty = case ty of
      TVar ref -> do
        -- Avoid infinite loops by tracking visited bindings
        if ref `elem` visited
          then return $ TVar $ Ident "_"
          else do
            b <- readIORef ref
            case b of
              Bound t -> sTypeToDisplayHelper (ref:visited) t
              Skolem i _ -> return $ TVar (unLocated i)
              Unbound _ idx -> return $ TVar $ Ident ("t" ++ show idx)
      TArrow t1 t2 -> do
        t1' <- sTypeToDisplayHelper visited t1
        t2' <- sTypeToDisplayHelper visited t2
        return $ TArrow t1' t2'
      TForall ref t -> do
        b <- readIORef ref
        case b of
          Bound t' -> sTypeToDisplayHelper (ref:visited) t'
          Skolem i _ -> do
            t' <- sTypeToDisplayHelper visited t
            return $ TForall (unLocated i) t'
          Unbound _ idx -> do
            t' <- sTypeToDisplayHelper visited t
            return $ TForall (Ident ("t" ++ show idx)) t'
      TConstraint traitName typeVars targetType bodyType -> do
        traitName' <- sTBindingToIdentImproved traitName
        typeVars' <- mapM sTBindingToIdentImproved typeVars
        targetType' <- sTypeToDisplayHelper visited targetType
        bodyType' <- sTypeToDisplayHelper visited bodyType
        return $ TConstraint traitName' typeVars' targetType' bodyType'
      TApp t1 t2 -> do
        t1' <- sTypeToDisplayHelper visited t1
        t2' <- sTypeToDisplayHelper visited t2
        return $ TApp t1' t2'
      TList t -> do
        t' <- sTypeToDisplayHelper visited t
        return $ TList t'
      TUnit -> return TUnit

sStmtToDisplay :: SStmt -> IO (Stmt Ident)
sStmtToDisplay = \case
  Let _ v mty body -> do
    v' <- sBindingToIdent v
    mty' <- mapM sTypeToDisplay mty
    -- Use targeted resolution for let statements with explicit type annotations
    body' <- case mty' of
      Just annotationType -> resolveTraitMethodsWithType body annotationType
      Nothing -> sExprToDisplay body
    return $ Let () v' mty' body'
  Type binding ty -> do
    binding' <- sTBindingToIdent binding
    ty' <- sTypeToDisplay ty
    return $ Type binding' ty'
  Data binding fields -> do
    binding' <- sTBindingToIdent binding
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ Data binding' fields'
  DataForall binding vars fields -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM sTBindingToIdent vars
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ DataForall binding' vars' fields'
  Trait binding vars methods -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM sTBindingToIdent vars
    methods' <- forM methods $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ Trait binding' vars' methods'
  TraitWithKinds binding vars methods -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM (sTBindingToIdent . fst) vars
    methods' <- forM methods $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ Trait binding' vars' methods'
  Impl binding vars ty methods -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM sTBindingToIdent vars
    ty' <- sTypeToDisplay ty
    methods' <- forM methods $ \(f, e) -> do
      e' <- sExprToDisplay e
      return (f, e')
    return $ Impl binding' vars' ty' methods'

sBlockToDisplayWithTypes :: SBlock -> IO (Block Ident)
sBlockToDisplayWithTypes (Block stmts expr) = do
  stmts' <- mapM sStmtToDisplay stmts
  expr' <- sExprToDisplayWithTypes expr
  return $ Block stmts' expr'

-- Create type mapping for expression variables
extractTypeMapping :: SExpr -> IO [(Ident, Type Ident)]
extractTypeMapping = gatherTypes
  where
    gatherTypes expr = case expr of
      Var _ binding -> do
        binding' <- sBindingToIdent binding
        exprType <- sTypeToDisplay (TVar (typeOf expr))
        return [(binding', exprType)]
      App _ t1 t2 -> do
        types1 <- gatherTypes t1
        types2 <- gatherTypes t2
        return (types1 ++ types2)
      Lam _ binding _ body -> do
        binding' <- sBindingToIdent binding
        exprType <- sTypeToDisplay (TVar (typeOf expr))
        bodyTypes <- gatherTypes body
        return ((binding', exprType) : bodyTypes)
      TyApp _ body _ -> gatherTypes body
      BlockExpr _ (Block stmts expr') -> do
        stmtTypes <- concat <$> mapM gatherStmtTypes stmts
        exprTypes <- gatherTypes expr'
        return (stmtTypes ++ exprTypes)
      RecordCreation _ expr' fields -> do
        exprTypes <- gatherTypes expr'
        fieldTypes <- concat <$> mapM (gatherTypes . snd) fields
        return (exprTypes ++ fieldTypes)
      PrimUnit _ -> return []
      PrimNil _ _ -> return []
      PrimCons _ _ headExpr tailExpr -> do
        headTypes <- gatherTypes headExpr
        tailTypes <- gatherTypes tailExpr
        return (headTypes ++ tailTypes)
      _ -> return []

    gatherStmtTypes stmt = case stmt of
      Let _ binding _ body -> do
        binding' <- sBindingToIdent binding
        exprType <- sTypeToDisplay (TVar (typeOf body))
        bodyTypes <- gatherTypes body
        return ((binding', exprType) : bodyTypes)
      Impl _ _ _ methods -> concat <$> mapM (gatherTypes . snd) methods
      _ -> return []

sBlockToDisplay :: SBlock -> IO (Block Ident)
sBlockToDisplay = sBlockToDisplayWithTypes
