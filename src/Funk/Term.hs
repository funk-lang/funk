module Funk.Term where

import Funk.Token

newtype Ident = Ident {unIdent :: String}
  deriving (Show, Eq, Ord)

data Type
  = TVar (Located Ident)
  | TArrow Type Type
  | TForall (Located Ident) Type
  deriving (Show, Eq)

data Term
  = Var (Located Ident)
  | Lam (Located Ident) (Maybe Type) Term
  | App Term Term
  | TyLam (Located Ident) Term
  | TyApp Term Type
  deriving (Show, Eq)
