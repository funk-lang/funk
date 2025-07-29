{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Term where

import Text.PrettyPrint hiding ((<>))

newtype Ident = Ident {unIdent :: String}
  deriving (Eq, Ord)

instance Show Ident where
  show = unIdent

data Precedence
  = AtomPrec
  | AppPrec
  | LamPrec
  | TyAppPrec
  | TyLamPrec
  | BlockPrec
  | ArrowPrec
  | ForallPrec
  deriving (Eq, Ord, Enum)

data Type b
  = TVar b
  | TArrow (Type b) (Type b)
  | TForall b (Type b)
  | TConstraint b [b] (Type b) (Type b)
  | TApp (Type b) (Type b)
  | TList (Type b)
  | TUnit
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
prettyType p (TConstraint traitName typeVars targetType bodyType) =
  let traitDoc = text $ show traitName
      typeVarsDoc = hsep (punctuate (text " ") (map (text . show) typeVars))
      targetDoc = prettyType AtomPrec targetType
      bodyDoc = prettyType ArrowPrec bodyType
   in parensIf (p > ArrowPrec) (traitDoc <+> typeVarsDoc <+> text "=>" <+> targetDoc <+> text "->" <+> bodyDoc)
prettyType p (TApp t1 t2) =
  let s1 = prettyType AppPrec t1
      s2 = prettyType AtomPrec t2
   in parensIf (p > AppPrec) (s1 <+> s2)
prettyType p (TList t) =
  let s = prettyType AtomPrec t
   in parensIf (p > AtomPrec) (text "#List" <+> s)
prettyType _ TUnit = text "#Unit"

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

instance Binding Ident where
  type BTVar Ident = Ident
  type BVar Ident = Maybe (Type Ident)
  type BLam Ident = Maybe (Type Ident)
  type BApp Ident = Maybe (Type Ident)
  type BTyApp Ident = Maybe (Type Ident)
  type BLet Ident = Maybe (Type Ident)
  type BBlock Ident = Maybe (Type Ident)
  type BRecord Ident = Maybe (Type Ident)
  type BRecordCreation Ident = Maybe (Type Ident)

data Expr b
  = Var (BVar b) b
  | Lam (BLam b) b (Maybe (Type (BTVar b))) (Expr b)
  | App (BApp b) (Expr b) (Expr b)
  | TyApp (BTyApp b) (Expr b) (Type (BTVar b))
  | BlockExpr (BBlock b) (Block b)
  | RecordType (BRecord b) b [(Ident, Type (BTVar b))]
  | RecordCreation (BRecordCreation b) (Expr b) [(Ident, Expr b)]
  | TraitMethod (BApp b) (BTVar b) [Type (BTVar b)] (Type (BTVar b)) Ident
  | PrimUnit (BVar b)
  | PrimNil (BVar b) (Type (BTVar b))
  | PrimCons (BVar b) (Type (BTVar b)) (Expr b) (Expr b)

data Stmt b
  = Let (BLet b) b (Maybe (Type (BTVar b))) (Expr b)
  | Type (BTVar b) (Type (BTVar b))
  | Data (BTVar b) [(Ident, Type (BTVar b))]
  | DataForall (BTVar b) [BTVar b] [(Ident, Type (BTVar b))]
  | Trait (BTVar b) [BTVar b] [(Ident, Type (BTVar b))]
  | TraitWithKinds (BTVar b) [(BTVar b, Maybe (Kind (BTVar b)))] [(Ident, Type (BTVar b))]
  | Impl (BTVar b) [BTVar b] (Type (BTVar b)) [(Ident, Expr b)]

prettyStmt :: Stmt Ident -> Doc
prettyStmt (Let letTy b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExprPrec AtomPrec body
      tyDoc = case mty of
        Just t -> text " :" <+> prettyType AtomPrec t
        Nothing -> case letTy of
          Just t -> text " :" <+> prettyType AtomPrec t
          Nothing -> empty
      letDoc = text "let" <+> (bStr <> tyDoc) <+> text "=" <+> bodyDoc
   in letDoc <> semi
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
      varsDoc =
        hsep
          ( punctuate
              (text ",")
              ( map
                  ( \(v, mk) -> case mk of
                      Just k -> text (show v) <+> text "::" <+> prettyKind AtomPrec k
                      Nothing -> text (show v)
                  )
                  vars
              )
          )
      methodsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) methods
   in text "trait" <+> bStr <+> varsDoc <+> braces (hsep (punctuate (text ",") methodsDoc))
prettyStmt (Impl b vars ty methods) =
  let bStr = text $ show b
      varsDoc = hsep (punctuate (text ",") (map (text . show) vars))
      tyDoc = prettyType AtomPrec ty
      methodsDoc = map (\(f, e) -> (text (unIdent f) <> text " =") <+> prettyExprPrec AtomPrec e) methods
   in text "instance" <+> bStr <+> varsDoc <+> text "for" <+> tyDoc <+> braces (hsep (punctuate (text ",") methodsDoc))

prettyExpr :: Expr Ident -> Doc
prettyExpr = prettyExprPrec AtomPrec

prettyExprPrec :: Precedence -> Expr Ident -> Doc
prettyExprPrec _ (Var varTy b) =
  case varTy of
    Just ty -> parens (text (show b) <+> text ":" <+> prettyType AtomPrec ty)
    Nothing -> text $ show b
prettyExprPrec p (Lam lamTy b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExprPrec LamPrec body
      tyDoc = case mty of
        Just t -> text ":" <+> prettyType AtomPrec t
        Nothing -> case lamTy of
          Just t -> text ":" <+> prettyType AtomPrec t
          Nothing -> empty
   in parensIf (p > LamPrec) (text "\\" <+> (bStr <> tyDoc) <+> text "->" <+> bodyDoc)
prettyExprPrec p (App appTy t1 t2) =
  let s1 = prettyExprPrec AppPrec t1
      s2 = prettyExprPrec AtomPrec t2
      result = parensIf (p > AppPrec) (s1 <+> s2)
   in case appTy of
        Just ty -> parens (result <+> text ":" <+> prettyType AtomPrec ty)
        Nothing -> result
prettyExprPrec p (TyApp tyAppTy t ty) =
  let s = prettyExprPrec TyAppPrec t
      tyDoc = prettyType AtomPrec ty
      result = parensIf (p > TyAppPrec) (s <+> brackets tyDoc)
   in case tyAppTy of
        Just resultTy -> parens (result <+> text ":" <+> prettyType AtomPrec resultTy)
        Nothing -> result
prettyExprPrec p (BlockExpr blockTy block) =
  let blockDoc = prettyBlock block
      result = parensIf (p > BlockPrec) blockDoc
   in case blockTy of
        Just ty -> parens (result <+> text ":" <+> prettyType AtomPrec ty)
        Nothing -> result
prettyExprPrec p (RecordType recordTy _ fields) =
  let fieldsDoc = map (\(f, ty) -> (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty) fields
      result = parensIf (p > AtomPrec) (braces (hsep (punctuate (text ",") fieldsDoc)))
   in case recordTy of
        Just ty -> parens (result <+> text ":" <+> prettyType AtomPrec ty)
        Nothing -> result
prettyExprPrec p (RecordCreation recordCreationTy expr fields) =
  let exprDoc = prettyExprPrec AtomPrec expr
      fieldsDoc = map (\(f, e) -> (text (unIdent f) <> text " =") <+> prettyExprPrec AtomPrec e) fields
      result = parensIf (p > AtomPrec) (exprDoc <+> braces (hsep (punctuate (text ",") fieldsDoc)))
   in case recordCreationTy of
        Just ty -> parens (result <+> text ":" <+> prettyType AtomPrec ty)
        Nothing -> result
prettyExprPrec p (TraitMethod methodTy traitName _ targetType methodName) =
  let traitDoc = text (show traitName)
      methodDoc = text (unIdent methodName)
      targetDoc = prettyType AtomPrec targetType
      result = parensIf (p > AppPrec) (traitDoc <> text "." <> methodDoc <> text "@" <> targetDoc)
   in case methodTy of
        Just ty -> parens (result <+> text ":" <+> prettyType AtomPrec ty)
        Nothing -> result
prettyExprPrec _ (PrimUnit unitTy) =
  case unitTy of
    Just ty -> parens (text "#Unit" <+> text ":" <+> prettyType AtomPrec ty)
    Nothing -> text "#Unit"
prettyExprPrec _ (PrimNil nilTy ty) =
  let result = text "#nil" <> brackets (prettyType AtomPrec ty)
   in case nilTy of
        Just resultTy -> parens (result <+> text ":" <+> prettyType AtomPrec resultTy)
        Nothing -> result
prettyExprPrec p (PrimCons consTy ty headExpr tailExpr) =
  let headDoc = prettyExprPrec AtomPrec headExpr
      tailDoc = prettyExprPrec AtomPrec tailExpr
      result = parensIf (p > AppPrec) ((text "#cons" <> brackets (prettyType AtomPrec ty)) <+> headDoc <+> tailDoc)
   in case consTy of
        Just resultTy -> parens (result <+> text ":" <+> prettyType AtomPrec resultTy)
        Nothing -> result

data Block b = Block [Stmt b] (Expr b)

prettyBlock :: Block Ident -> Doc
prettyBlock (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExprPrec AtomPrec expr
   in braces (stmtsDoc $$ exprDoc)

showBlock :: Block Ident -> String
showBlock block = render $ prettyBlock block

prettyFile :: Block Ident -> Doc
prettyFile (Block stmts expr) =
  let stmtsDoc = vcat $ map prettyStmt stmts
      exprDoc = prettyExprPrec AtomPrec expr
   in stmtsDoc $$ exprDoc

showFile :: Block Ident -> String
showFile block = render $ prettyFile block
