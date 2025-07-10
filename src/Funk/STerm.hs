{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.STerm where

import Data.IORef
import Funk.Term
import Funk.Token
import Text.Parsec

data TBinding
  = Bound (Type STBinding)
  | Skolem (Located Ident) Int
  | Unbound SourcePos Int

showTBinding :: TBinding -> IO String
showTBinding (Bound ty) = showSType ty
showTBinding (Skolem i _) = return $ unIdent (unLocated i)
showTBinding (Unbound _ idx) = return $ "_" ++ show idx

type STBinding = IORef TBinding

bindingPos :: STBinding -> IO SourcePos
bindingPos ref = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

type SType = Type STBinding

showSType :: SType -> IO String
showSType (TVar ref) = do
  b <- readIORef ref
  showTBinding b
showSType (TArrow t1 t2) = do
  s1 <- showSType t1
  s2 <- showSType t2
  return $ "(" ++ s1 ++ " -> " ++ s2 ++ ")"
showSType (TForall ref t) = do
  b <- readIORef ref
  bStr <- showTBinding b
  st <- showSType t
  return $ "(\\ " ++ bStr ++ " . " ++ st ++ ")"
showSType (TLam ref t) = do
  b <- readIORef ref
  bStr <- showTBinding b
  tStr <- showSType t
  return $ "(/\\ " ++ bStr ++ " . " ++ tStr ++ ")"

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

instance Binding SBinding where
  type BTVar SBinding = STBinding
  type BVar SBinding = STBinding
  type BLam SBinding = SLam
  type BApp SBinding = STBinding
  type BTyLam SBinding = STBinding
  type BTyApp SBinding = STBinding
  type BLet SBinding = STBinding
  type BBlock SBinding = STBinding

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

showSExpr :: SExpr -> IO String
showSExpr (Var _ ref) = do
  v <- readIORef (unSBinding ref)
  case v of
    VBound t -> showSExpr t
    VUnbound i -> return $ unIdent (unLocated i)
showSExpr (Lam ty ref _ body) = do
  v <- readIORef (unSBinding ref)
  bodyStr <- showSExpr body
  tyBinding <- readIORef $ sLamInput ty
  tyStr <- showTBinding tyBinding
  case v of
    VBound t -> do
      tStr <- showSExpr t
      return $ "(\\ " ++ tStr ++ " : " ++ tyStr ++ " . " ++ bodyStr ++ ")"
    VUnbound i ->
      return $ "(\\ " ++ unIdent (unLocated i) ++ " : " ++ tyStr ++ " . " ++ bodyStr ++ ")"
showSExpr (App _ t1 t2) = do
  s1 <- showSExpr t1
  s2 <- showSExpr t2
  return $ "(" ++ s1 ++ " " ++ s2 ++ ")"
showSExpr (TyApp _ t ty) = do
  s <- showSExpr t
  tyStr <- showSType ty
  return $ "(" ++ s ++ " [" ++ tyStr ++ "])"
showSExpr (TyLam _ ref body) = do
  v <- readIORef ref
  bodyStr <- showSExpr body
  case v of
    Bound t -> do
      tStr <- showSType t
      return $ "/\\ " ++ tStr ++ " . " ++ bodyStr
    Skolem i _ ->
      return $ "/\\ " ++ unIdent (unLocated i) ++ " . " ++ bodyStr
    Unbound _ idx ->
      return $ "/\\ _" ++ show idx ++ " . " ++ bodyStr
showSExpr (BlockExpr _ block) = showSBlock block

showSStmt :: SStmt -> IO String
showSStmt (Let _ ref _ body) = do
  v <- readIORef (unSBinding ref)
  bodyStr <- showSExpr body
  case v of
    VBound t -> do
      tStr <- showSExpr t
      return $ tStr ++ " = " ++ bodyStr ++ ";"
    VUnbound i ->
      return $ unIdent (unLocated i) ++ " = " ++ bodyStr ++ ";"
showSStmt (Type ref ty) = do
  v <- readIORef (unSBinding ref)
  tyStr <- showSType ty
  case v of
    VBound t -> do
      tStr <- showSExpr t
      return $ "type " ++ tStr ++ " = " ++ tyStr ++ ";"
    VUnbound i ->
      return $ "type " ++ unIdent (unLocated i) ++ " = " ++ tyStr ++ ";"

showSBlock :: SBlock -> IO String
showSBlock (Block stmts expr) = do
  stmtsStr <- mapM showSStmt stmts
  exprStr <- showSExpr expr
  return $ "{\n" ++ unlines stmtsStr ++ exprStr ++ "\n}"
