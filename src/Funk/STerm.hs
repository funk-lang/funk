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

sBindingToIdent :: SBinding -> IO Ident
sBindingToIdent (SBinding ref) = do
  b <- readIORef ref
  case b of
    VBound _ -> return $ Ident "_"
    VUnbound i -> return $ unLocated i

smartResolveTargetType :: SType -> STBinding -> IO (Type Ident)
smartResolveTargetType targetType exprType = do
  normalResult <- sTypeToDisplay targetType
  case normalResult of
    TVar (Ident tname) | take 1 tname == "t" -> do
      exprTypeResolved <- sTypeToDisplay (TVar exprType)
      case exprTypeResolved of
        TApp (TVar constructor) _ -> return $ TVar constructor
        TVar constructor -> return $ TVar constructor
        _ -> return normalResult
    _ -> return normalResult

aggressiveTypeResolve :: SType -> IO (Type Ident)
aggressiveTypeResolve stype = do
  result <- sTypeToDisplay stype
  case result of
    TVar (Ident tname) | take 1 tname == "t" -> do
      case stype of
        TVar ref -> do
          binding <- readIORef ref
          case binding of
            Bound boundType -> aggressiveTypeResolve boundType
            _ -> return result
        _ -> return result
    _ -> return result

resolveTraitMethodTargets :: SExpr -> IO (Expr Ident)
resolveTraitMethodTargets sexpr = do
  normalExpr <- sExprToDisplayWithTypes sexpr
  contextResolveExpr normalExpr (typeOf sexpr)

resolveTraitMethodsWithType :: SExpr -> Type Ident -> IO (Expr Ident)
resolveTraitMethodsWithType sexpr expectedType = do
  normalExpr <- sExprToDisplayWithTypes sexpr
  directResolveWithType normalExpr expectedType

directResolveWithType :: Expr Ident -> Type Ident -> IO (Expr Ident)
directResolveWithType expr expectedType = case expr of
  App appTy f arg -> do
    f' <- directResolveWithType f expectedType
    arg' <- directResolveWithType arg expectedType
    return $ App appTy f' arg'
  TraitMethod methodTy traitName typeArgs (TVar (Ident tname)) methodName
    | take 1 tname == "t" -> do
        case expectedType of
          TApp constructor _ ->
            return $ TraitMethod methodTy traitName typeArgs constructor methodName
          _ -> return expr
  _ -> return expr

contextResolveExpr :: Expr Ident -> STBinding -> IO (Expr Ident)
contextResolveExpr expr exprType = case expr of
  App appTy f arg -> do
    exprTypeResolved <- sTypeToDisplay (TVar exprType)
    f' <- case f of
      TraitMethod methodTy traitName typeArgs (TVar (Ident tname)) methodName
        | take 1 tname == "t" -> do
            case exprTypeResolved of
              TApp constructor _ ->
                return $ TraitMethod methodTy traitName typeArgs constructor methodName
              _ -> return f
      _ -> contextResolveExpr f exprType
    return $ App appTy f' arg
  TraitMethod methodTy traitName typeArgs (TVar (Ident tname)) methodName
    | take 1 tname == "t" -> do
        exprTypeResolved <- sTypeToDisplay (TVar exprType)
        case exprTypeResolved of
          TApp constructor _ ->
            return $ TraitMethod methodTy traitName typeArgs constructor methodName
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

sExprToDisplayWithTypes :: SExpr -> IO (Expr Ident)
sExprToDisplayWithTypes sexpr = case sexpr of
  Var _ binding -> do
    binding' <- sBindingToIdent binding
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ Var ty' binding'
  App _ t1 t2 -> do
    t1' <- sExprToDisplayWithTypes t1
    t2' <- sExprToDisplayWithTypes t2
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ App ty' t1' t2'
  Lam _ binding mty body -> do
    binding' <- sBindingToIdent binding
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    mty' <- case mty of
      Just ty -> Just <$> sTypeToDisplay ty
      Nothing -> Just <$> sTypeToDisplay (TVar (typeOf sexpr))
    body' <- sExprToDisplayWithTypes body
    return $ Lam ty' binding' mty' body'
  TyApp _ body outTy -> do
    body' <- sExprToDisplayWithTypes body
    outTy' <- sTypeToDisplay outTy
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ TyApp ty' body' outTy'
  BlockExpr _ block -> do
    block' <- sBlockToDisplayWithTypes block
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ BlockExpr ty' block'
  RecordType _ v fields -> do
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    v' <- sBindingToIdent v
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ RecordType ty' v' fields'
  RecordCreation _ expr fields -> do
    expr' <- sExprToDisplayWithTypes expr
    fields' <- forM fields $ \(f, e) -> do
      e' <- sExprToDisplayWithTypes e
      return (f, e')
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ RecordCreation ty' expr' fields'
  TraitMethod _ traitName typeArgs targetType methodName -> do
    traitName' <- sTBindingToIdent traitName
    typeArgs' <- mapM sTypeToDisplay typeArgs
    targetType' <- aggressiveTypeResolve targetType
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ TraitMethod ty' traitName' typeArgs' targetType' methodName
  PrimUnit _ -> do
    ty' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ PrimUnit ty'
  PrimNil _ ty -> do
    ty' <- sTypeToDisplay ty
    exprTy' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ PrimNil exprTy' ty'
  PrimCons _ ty headExpr tailExpr -> do
    ty' <- sTypeToDisplay ty
    head' <- sExprToDisplayWithTypes headExpr
    tail' <- sExprToDisplayWithTypes tailExpr
    exprTy' <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ PrimCons exprTy' ty' head' tail'

sExprToDisplay :: SExpr -> IO (Expr Ident)
sExprToDisplay = sExprToDisplayWithTypes

sTypeToDisplay :: SType -> IO (Type Ident)
sTypeToDisplay = sTypeToDisplayHelper []
  where
    sTypeToDisplayHelper :: [STBinding] -> SType -> IO (Type Ident)
    sTypeToDisplayHelper visited ty = case ty of
      TVar ref -> do
        if ref `elem` visited
          then return $ TVar $ Ident "_"
          else do
            b <- readIORef ref
            case b of
              Bound t -> sTypeToDisplayHelper (ref : visited) t
              Skolem i _ -> return $ TVar (unLocated i)
              Unbound _ idx -> return $ TVar $ Ident ("t" ++ show idx)
      TArrow t1 t2 -> do
        t1' <- sTypeToDisplayHelper visited t1
        t2' <- sTypeToDisplayHelper visited t2
        return $ TArrow t1' t2'
      TForall ref t -> do
        b <- readIORef ref
        case b of
          Bound t' -> sTypeToDisplayHelper (ref : visited) t'
          Skolem i _ -> do
            t' <- sTypeToDisplayHelper visited t
            return $ TForall (unLocated i) t'
          Unbound _ idx -> do
            t' <- sTypeToDisplayHelper visited t
            return $ TForall (Ident ("t" ++ show idx)) t'
      TConstraint traitName typeVars targetType bodyType -> do
        traitName' <- sTBindingToIdent traitName
        typeVars' <- mapM sTBindingToIdent typeVars
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
  Let letTy v mty body -> do
    v' <- sBindingToIdent v
    mty' <- mapM sTypeToDisplay mty
    letTy' <- sTypeToDisplay (TVar letTy)
    body' <- case mty' of
      Just annotationType -> resolveTraitMethodsWithType body annotationType
      Nothing -> sExprToDisplay body
    return $ Let letTy' v' mty' body'
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
    let go (v, _) = do
          ref <- sTBindingToIdent v
          return (ref, Nothing) -- TODO kind information is not handled here
    vars' <- mapM go vars
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

sBlockToDisplay :: SBlock -> IO (Block Ident)
sBlockToDisplay = sBlockToDisplayWithTypes
