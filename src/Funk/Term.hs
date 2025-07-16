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
  | TApp (Type b) (Type b)
  deriving (Show, Eq)

data Kind b
  = KVar b
  | KStar
  | KArrow (Kind b) (Kind b)
  deriving (Show, Eq)

prettyKind :: (Show b) => Precedence -> Kind b -> Doc
prettyKind _ (KVar b) = text $ show b
prettyKind _ KStar = text "*"
prettyKind p (KArrow k1 k2) =
  let s1 = prettyKind (succ ArrowPrec) k1
      s2 = prettyKind ArrowPrec k2
   in parensIf (p > ArrowPrec) (s1 <+> text "->" <+> s2)

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
prettyType p (TApp t1 t2) =
  let s1 = prettyType AppPrec t1
      s2 = prettyType AtomPrec t2
   in parensIf (p > AppPrec) (s1 <+> s2)

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
  | TraitMethod (BApp b) (BTVar b) [Type (BTVar b)] (Type (BTVar b)) Ident

data Stmt b
  = Let (BLet b) b (Maybe (Type (BTVar b))) (Expr b)
  | Type (BTVar b) (Type (BTVar b))
  | Data (BTVar b) [(Ident, Type (BTVar b))]
  | DataForall (BTVar b) [BTVar b] [(Ident, Type (BTVar b))]
  | Trait (BTVar b) [BTVar b] [(Ident, Type (BTVar b))]
  | TraitWithKinds (BTVar b) [(BTVar b, Maybe (Kind (BTVar b)))] [(Ident, Type (BTVar b))]
  | Impl (BTVar b) [BTVar b] (Type (BTVar b)) [(Ident, Expr b)]

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
prettyStmt (Trait b vars methods) =
  let bStr = text $ show b
      varsDoc = hsep (punctuate (text ",") (map (text . show) vars))
      methodsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) methods
   in text "trait" <+> bStr <+> varsDoc <+> braces (hsep (punctuate (text ",") methodsDoc))
prettyStmt (TraitWithKinds b vars methods) =
  let bStr = text $ show b
      varsDoc = hsep (punctuate (text ",") (map (\(v, mk) -> case mk of
        Just k -> text (show v) <+> text "::" <+> prettyKind AtomPrec k
        Nothing -> text (show v)) vars))
      methodsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) methods
   in text "trait" <+> bStr <+> varsDoc <+> braces (hsep (punctuate (text ",") methodsDoc))
prettyStmt (Impl b vars ty methods) =
  let bStr = text $ show b
      varsDoc = hsep (punctuate (text ",") (map (text . show) vars))
      tyDoc = prettyType AtomPrec ty
      methodsDoc = map (\(f, e) -> (text (unIdent f) <> text " =") <+> prettyExpr AtomPrec e) methods
   in text "instance" <+> bStr <+> varsDoc <+> text "for" <+> tyDoc <+> braces (hsep (punctuate (text ",") methodsDoc))

prettyExpr :: (Show (BTVar b), Show b) => Precedence -> Expr b -> Doc
prettyExpr _ (Var _ b) = text $ show b
prettyExpr p (Lam _ b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExpr LamPrec body
      tyDoc = case mty of
        Just t -> text ":" <+> prettyType AtomPrec t
        Nothing -> empty
   in parensIf (p > LamPrec) (text "\\" <+> (bStr <> tyDoc) <+> text "->" <+> bodyDoc)
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
      fieldsDoc = map (\(f, e) -> (text (unIdent f) <> text " =") <+> prettyExpr AtomPrec e) fields
   in parensIf (p > AtomPrec) (exprDoc <+> braces (hsep (punctuate (text ",") fieldsDoc)))
prettyExpr p (TraitMethod _ traitName typeArgs targetType methodName) =
  let traitDoc = text (show traitName)
      methodDoc = text (unIdent methodName)
      targetDoc = prettyType AtomPrec targetType
   in parensIf (p > AppPrec) (traitDoc <> text "." <> methodDoc <> text "@" <> targetDoc)

-- Enhanced pretty printing that shows types for all expressions
prettyExprWithTypes :: (Show (BTVar b), Show b, Eq b) => [(b, Type (BTVar b))] -> Precedence -> Expr b -> Doc
prettyExprWithTypes typeMap _ (Var _ b) =
  case lookup b typeMap of
    Just ty -> parens (text (show b) <+> text ":" <+> prettyType AtomPrec ty)
    Nothing -> text $ show b
prettyExprWithTypes typeMap p (Lam _ b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExprWithTypes typeMap LamPrec body
      tyDoc = case mty of
        Just t -> text ":" <+> prettyType AtomPrec t
        Nothing -> empty
   in parensIf (p > LamPrec) (text "\\" <+> (bStr <> tyDoc) <+> text "." <+> bodyDoc)
prettyExprWithTypes typeMap p (App _ t1 t2) =
  let s1 = prettyExprWithTypes typeMap AppPrec t1
      s2 = prettyExprWithTypes typeMap AtomPrec t2
   in parensIf (p > AppPrec) (s1 <+> s2)
prettyExprWithTypes typeMap p (TyApp _ t ty) =
  let s = prettyExprWithTypes typeMap TyAppPrec t
      tyDoc = prettyType AtomPrec ty
   in parensIf (p > TyAppPrec) (s <+> brackets tyDoc)
prettyExprWithTypes typeMap p (BlockExpr _ block) =
  let blockDoc = prettyBlockWithTypes typeMap block
   in parensIf (p > BlockPrec) blockDoc
prettyExprWithTypes typeMap p (RecordType _ _ fields) =
  let fieldsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) fields
   in parensIf (p > AtomPrec) (braces (hsep (punctuate (text ",") fieldsDoc)))
prettyExprWithTypes typeMap p (RecordCreation _ expr fields) =
  let exprDoc = prettyExprWithTypes typeMap AtomPrec expr
      fieldsDoc = map (\(f, e) -> (text (unIdent f) <> text ":") <+> prettyExprWithTypes typeMap AtomPrec e) fields
   in parensIf (p > AtomPrec) (exprDoc <+> braces (hsep (punctuate (text ",") fieldsDoc)))
prettyExprWithTypes typeMap p (TraitMethod _ traitName typeArgs targetType methodName) =
  let traitDoc = text (show traitName)
      methodDoc = text (unIdent methodName)
      targetDoc = prettyType AtomPrec targetType
   in parensIf (p > AppPrec) (traitDoc <> text "." <> methodDoc <> text "@" <> targetDoc)

data Block b = Block [Stmt b] (Expr b)

prettyBlock :: (Show (BTVar b), Show b) => Block b -> Doc
prettyBlock (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExpr AtomPrec expr
   in braces (stmtsDoc $$ exprDoc)

prettyBlockWithTypes :: (Show (BTVar b), Show b, Eq b) => [(b, Type (BTVar b))] -> Block b -> Doc
prettyBlockWithTypes typeMap (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExprWithTypes typeMap AtomPrec expr
   in braces (stmtsDoc $$ exprDoc)

showBlock :: (Show (BTVar b), Show b) => Block b -> String
showBlock block = render $ prettyBlock block

prettyFile :: (Show (BTVar b), Show b) => Block b -> Doc
prettyFile (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExpr AtomPrec expr
   in stmtsDoc $$ exprDoc

prettyFileWithTypes :: (Show (BTVar b), Show b, Eq b) => [(b, Type (BTVar b))] -> Block b -> Doc
prettyFileWithTypes typeMap (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExprWithTypes typeMap AtomPrec expr
   in stmtsDoc $$ exprDoc

showFile :: (Show (BTVar b), Show b) => Block b -> String
showFile block = render $ prettyFile block

showFileWithTypes :: (Show (BTVar b), Show b, Eq b) => [(b, Type (BTVar b))] -> Block b -> String
showFileWithTypes typeMap block = render $ prettyFileWithTypes typeMap block
