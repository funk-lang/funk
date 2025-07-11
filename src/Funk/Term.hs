{-# LANGUAGE TypeFamilies #-}

module Funk.Term where

import Text.Parsec

newtype Ident = Ident {unIdent :: String}
  deriving (Show, Eq, Ord)

data Type b
  = TVar b
  | TArrow (Type b) (Type b)
  | TForall b (Type b)
  | TLam b (Type b)
  deriving (Show, Eq)

class Binding b where
  type BTVar b
  type BVar b
  type BLam b
  type BApp b
  type BTyLam b
  type BTyApp b
  type BLet b
  type BBlock b
  type BRecord b
  type BRecordCreation b
  type BRecord b = SourcePos

data Expr b
  = Var (BVar b) b
  | Lam (BLam b) b (Maybe (Type (BTVar b))) (Expr b)
  | App (BApp b) (Expr b) (Expr b)
  | TyApp (BTyApp b) (Expr b) (Type (BTVar b))
  | TyLam (BTyLam b) (BTVar b) (Expr b)
  | BlockExpr (BBlock b) (Block b)
  | RecordType (BRecord b) b [(Ident, Type (BTVar b))]
  | RecordCreation (BRecordCreation b) (Expr b) [(Ident, Expr b)]

data Stmt b = Let (BLet b) b (Maybe (Type (BTVar b))) (Expr b) | Type (BTVar b) (Type (BTVar b)) | Data (BTVar b) [(Ident, Type (BTVar b))]

data Block b = Block [Stmt b] (Expr b)
