{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.STerm where

import Control.Monad (forM)
import Data.IORef
import Funk.Term
import Funk.Token
import Text.Parsec

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
typePos (TApp t1 _) = typePos t1


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

-- Enhanced version that includes type information for display
sExprToDisplayWithTypes :: SExpr -> IO (Expr Ident)
sExprToDisplayWithTypes sexpr = case sexpr of
  Var _ binding -> do
    binding' <- sBindingToIdent binding
    -- For variables, we'll add the type as a synthetic lambda annotation
    exprType <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ Var () binding'
  App _ t1 t2 -> do
    t1' <- sExprToDisplayWithTypes t1
    t2' <- sExprToDisplayWithTypes t2
    return $ App () t1' t2'
  Lam _ binding mty body -> do
    binding' <- sBindingToIdent binding
    -- Extract the actual inferred type
    exprType <- sTypeToDisplay (TVar (typeOf sexpr))
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
    targetType' <- sTypeToDisplay targetType
    return $ TraitMethod () traitName' typeArgs' targetType' methodName

-- Original version for backward compatibility
sExprToDisplay :: SExpr -> IO (Expr Ident)
sExprToDisplay = sExprToDisplayWithTypes

sTypeToDisplay :: SType -> IO (Type Ident)
sTypeToDisplay = \case
  TVar ref -> do
    b <- readIORef ref
    case b of
      Bound t -> sTypeToDisplay t
      Skolem i _ -> return $ TVar (unLocated i)
      Unbound _ _ -> return $ TVar $ Ident "_"
  TArrow t1 t2 -> do
    t1' <- sTypeToDisplay t1
    t2' <- sTypeToDisplay t2
    return $ TArrow t1' t2'
  TForall ref ty -> do
    b <- readIORef ref
    case b of
      Bound t -> sTypeToDisplay t
      Skolem i _ -> do
        ty' <- sTypeToDisplay ty
        return $ TForall (unLocated i) ty'
      Unbound _ _ -> do
        ty' <- sTypeToDisplay ty
        return $ TForall (Ident "_") ty'
  TApp t1 t2 -> do
    t1' <- sTypeToDisplay t1
    t2' <- sTypeToDisplay t2
    -- If t1 is a Skolem type constructor, just return its name instead of the full application
    case t1' of
      TVar (Ident name) | name /= "_" -> return $ TVar (Ident name)
      _ -> return $ TApp t1' t2'

sStmtToDisplay :: SStmt -> IO (Stmt Ident)
sStmtToDisplay = \case
  Let _ v mty body -> do
    v' <- sBindingToIdent v
    mty' <- mapM sTypeToDisplay mty
    body' <- sExprToDisplay body
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
    vars' <- mapM sTBindingToIdent (map fst vars)
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
extractTypeMapping sexpr = gatherTypes sexpr
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
