{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Term where

import Text.Parsec
import Text.PrettyPrint hiding ((<>))

newtype Ident = Ident {unIdent :: String}
  deriving (Eq, Ord)

instance Show Ident where
  show = unIdent

data Precedence = AtomPrec | AppPrec | LamPrec | TyAppPrec | TyLamPrec | BlockPrec | ArrowPrec | ForallPrec
  deriving (Eq, Ord, Enum)

data Type b
  = TVar b
  | TArrow (Type b) (Type b)
  | TForall b (Type b)
  deriving (Show, Eq)

prettyType :: (Show b) => Precedence -> Type b -> Doc
prettyType _ (TVar b) = text $ show b
prettyType p (TArrow t1 t2) =
  let s1 = prettyType (succ ArrowPrec) t1
      s2 = prettyType ArrowPrec t2
   in parensIf (p > ArrowPrec) (s1 <+> text "->" <+> s2)
prettyType p (TForall ref t) =
  let bStr = text $ show ref
      st = prettyType ForallPrec t
   in parensIf (p > ForallPrec) (text "forall" <+> bStr <+> text "." <+> st)

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

class Binding b where
  type BTVar b
  type BVar b
  type BLam b
  type BApp b
  type BTyApp b
  type BLet b
  type BBlock b
  type BRecord b
  type BRecordCreation b
  type BRecord b = SourcePos

instance Binding Ident where
  type BTVar Ident = Ident
  type BVar Ident = ()
  type BLam Ident = ()
  type BApp Ident = ()
  type BTyApp Ident = ()
  type BLet Ident = ()
  type BBlock Ident = ()
  type BRecord Ident = ()
  type BRecordCreation Ident = ()

data Expr b
  = Var (BVar b) b
  | Lam (BLam b) b (Maybe (Type (BTVar b))) (Expr b)
  | App (BApp b) (Expr b) (Expr b)
  | TyApp (BTyApp b) (Expr b) (Type (BTVar b))
  | BlockExpr (BBlock b) (Block b)
  | RecordType (BRecord b) b [(Ident, Type (BTVar b))]
  | RecordCreation (BRecordCreation b) (Expr b) [(Ident, Expr b)]

data Stmt b
  = Let (BLet b) b (Maybe (Type (BTVar b))) (Expr b)
  | Type (BTVar b) (Type (BTVar b))
  | Data (BTVar b) [(Ident, Type (BTVar b))]
  | DataForall (BTVar b) [BTVar b] [(Ident, Type (BTVar b))]

prettyStmt :: (Show b, Show (BTVar b)) => Stmt b -> Doc
prettyStmt (Let _ b _ body) =
  let bStr = text $ show b
      bodyDoc = prettyExpr AtomPrec body
   in (text "let" <+> bStr <+> text "=" <+> bodyDoc) <> semi
prettyStmt (Type b t) =
  (text "type" <+> text (show b) <+> text "=" <+> prettyType AtomPrec t) <> semi
prettyStmt (Data b fields) =
  let bStr = text $ show b
      fieldsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) fields
   in text "data" <+> bStr <+> braces (hsep (punctuate (text ",") fieldsDoc))
prettyStmt (DataForall b vars fields) =
  let bStr = text $ show b
      varsDoc = hsep (punctuate (text ",") (map (text . show) vars))
      fieldsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) fields
   in text "data" <+> bStr <+> text "=" <+> text "forall" <+> varsDoc <+> text "." <+> braces (hsep (punctuate (text ",") fieldsDoc))

prettyExpr :: (Show (BTVar b), Show b) => Precedence -> Expr b -> Doc
prettyExpr _ (Var _ b) = text $ show b
prettyExpr p (Lam _ b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExpr LamPrec body
      tyDoc = case mty of
        Just t -> text ":" <+> prettyType AtomPrec t
        Nothing -> empty
   in parensIf (p > LamPrec) (text "\\" <+> (bStr <> tyDoc) <+> text "." <+> bodyDoc)
prettyExpr p (App _ t1 t2) =
  let s1 = prettyExpr AppPrec t1
      s2 = prettyExpr AtomPrec t2
   in parensIf (p > AppPrec) (s1 <+> s2)
prettyExpr p (TyApp _ t ty) =
  let s = prettyExpr TyAppPrec t
      tyDoc = prettyType AtomPrec ty
   in parensIf (p > TyAppPrec) (s <+> brackets tyDoc)
prettyExpr p (BlockExpr _ block) =
  let blockDoc = prettyBlock block
   in parensIf (p > BlockPrec) blockDoc
prettyExpr p (RecordType _ _ fields) =
  let fieldsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) fields
   in parensIf (p > AtomPrec) (braces (hsep (punctuate (text ",") fieldsDoc)))
prettyExpr p (RecordCreation _ expr fields) =
  let exprDoc = prettyExpr AtomPrec expr
      fieldsDoc = map (\(f, e) -> (text (unIdent f) <> text ":") <+> prettyExpr AtomPrec e) fields
   in parensIf (p > AtomPrec) (exprDoc <+> braces (hsep (punctuate (text ",") fieldsDoc)))

data Block b = Block [Stmt b] (Expr b)

prettyBlock :: (Show (BTVar b), Show b) => Block b -> Doc
prettyBlock (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExpr AtomPrec expr
   in braces (stmtsDoc $$ exprDoc)

showBlock :: (Show (BTVar b), Show b) => Block b -> String
showBlock block = render $ prettyBlock block

prettyFile :: (Show (BTVar b), Show b) => Block b -> Doc
prettyFile (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExpr AtomPrec expr
   in stmtsDoc $$ exprDoc

showFile :: (Show (BTVar b), Show b) => Block b -> String
showFile block = render $ prettyFile block
