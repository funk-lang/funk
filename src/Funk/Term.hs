module Funk.Term where

newtype Ident = Ident {unIdent :: String}
  deriving (Show, Eq, Ord)

data Type b
  = TVar b
  | TArrow (Type b) (Type b)
  | TForall b (Type b)
  deriving (Show, Eq)

data Term f ty b
  = Var b
  | Lam b (f (Type ty)) (Term f ty b)
  | App (Term f ty b) (Term f ty b)
  | TyLam ty (Term f ty b)
  | TyApp (Term f ty b) (Type ty)
