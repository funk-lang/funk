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
  return $ "(\\/ " ++ bStr ++ " . " ++ st ++ ")"

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

data Var = VBound STerm | VUnbound (Located Ident)

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

type STerm = Term SBinding

typeOf :: STerm -> STBinding
typeOf = \case
  Var ty _ -> ty
  App ty _ _ -> ty
  Lam (SLam _ ty) _ _ _ -> ty
  TyLam ty _ _ -> ty
  TyApp ty _ _ -> ty
  Let ty _ _ _ _ -> ty

showSTerm :: STerm -> IO String
showSTerm (Var _ ref) = do
  v <- readIORef (unSBinding ref)
  case v of
    VBound t -> showSTerm t
    VUnbound i -> return $ unIdent (unLocated i)
showSTerm (Lam ty ref _ body) = do
  v <- readIORef (unSBinding ref)
  bodyStr <- showSTerm body
  tyBinding <- readIORef $ sLamInput ty
  tyStr <- showTBinding tyBinding
  case v of
    VBound t -> do
      tStr <- showSTerm t
      return $ "(\\ " ++ tStr ++ " : " ++ tyStr ++ " . " ++ bodyStr ++ ")"
    VUnbound i ->
      return $ "(\\ " ++ unIdent (unLocated i) ++ " : " ++ tyStr ++ " . " ++ bodyStr ++ ")"
showSTerm (App _ t1 t2) = do
  s1 <- showSTerm t1
  s2 <- showSTerm t2
  return $ "(" ++ s1 ++ " " ++ s2 ++ ")"
showSTerm (TyLam _ ref body) = do
  b <- readIORef ref
  bStr <- showTBinding b
  bodyStr <- showSTerm body
  return $ "(/\\ " ++ bStr ++ " . " ++ bodyStr ++ ")"
showSTerm (TyApp _ t ty) = do
  s <- showSTerm t
  tyStr <- showSType ty
  return $ "(" ++ s ++ " [" ++ tyStr ++ "])"
showSTerm (Let _ ref _ body scope) = do
  v <- readIORef (unSBinding ref)
  bodyStr <- showSTerm body
  scopeStr <- showSTerm scope
  case v of
    VBound t -> do
      tStr <- showSTerm t
      return $ tStr ++ " = " ++ bodyStr ++ "; " ++ scopeStr ++ ")"
    VUnbound i ->
      return $  unIdent (unLocated i) ++ " = " ++ bodyStr ++ "; " ++ scopeStr ++ ")"
