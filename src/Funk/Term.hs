{-# LANGUAGE TypeFamilies #-}

module Funk.Term where

newtype Ident = Ident {unIdent :: String}
  deriving (Show, Eq, Ord)

data Type b
  = TVar b
  | TArrow (Type b) (Type b)
  | TForall b (Type b)
  deriving (Show, Eq)

class Binding b where
  type BTVar b
  type BVar b
  type BLam b
  type BApp b
  type BTyLam b
  type BTyApp b

data Term b
  = Var (BVar b) b
  | Lam (BLam b) b (Maybe (Type (BTVar b))) (Term b)
  | App (BApp b) (Term b) (Term b)
  | TyLam (BTyLam b) (BTVar b) (Term b)
  | TyApp (BTyApp b) (Term b) (Type (BTVar b))
