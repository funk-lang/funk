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

type STBinding = IORef TBinding

bindingPos :: STBinding -> IO SourcePos
bindingPos ref = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

type SType = Type STBinding

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
typePos (TLam ref _) = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

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
  type BTyLam SBinding = STBinding
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
  TyLam ty _ _ -> ty
  BlockExpr ty _ -> ty
  RecordType ty _ _ -> ty
  RecordCreation ty _ _ -> ty

sExprToDisplay :: SExpr -> IO (Expr Ident)
sExprToDisplay = \case
  Var _ binding -> do
    binding' <- sBindingToIdent binding
    return $ Var () binding'
  App _ t1 t2 -> do
    t1' <- sExprToDisplay t1
    t2' <- sExprToDisplay t2
    return $ App () t1' t2'
  Lam _ binding mty body -> do
    binding' <- sBindingToIdent binding
    mty' <- mapM sTypeToDisplay mty
    body' <- sExprToDisplay body
    return $ Lam () binding' mty' body'
  TyApp _ body outTy -> do
    body' <- sExprToDisplay body
    outTy' <- sTypeToDisplay outTy
    return $ TyApp () body' outTy'
  TyLam _ v body -> do
    v' <- sTBindingToIdent v
    body' <- sExprToDisplay body
    return $ TyLam () v' body'
  BlockExpr _ block -> do
    block' <- sBlockToDisplay block
    return $ BlockExpr () block'
  RecordType _ v fields -> do
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    v' <- sBindingToIdent v
    return $ RecordType () v' fields'
  RecordCreation _ expr fields -> do
    expr' <- sExprToDisplay expr
    fields' <- forM fields $ \(f, e) -> do
      e' <- sExprToDisplay e
      return (f, e')
    return $ RecordCreation () expr' fields'

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
  TLam ref ty -> do
    b <- readIORef ref
    case b of
      Bound t -> sTypeToDisplay t
      Skolem i _ -> do
        ty' <- sTypeToDisplay ty
        return $ TLam (unLocated i) ty'
      Unbound _ _ -> do
        ty' <- sTypeToDisplay ty
        return $ TLam (Ident "_") ty'

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

sBlockToDisplay :: SBlock -> IO (Block Ident)
sBlockToDisplay (Block stmts expr) = do
  stmts' <- mapM sStmtToDisplay stmts
  expr' <- sExprToDisplay expr
  return $ Block stmts' expr'
