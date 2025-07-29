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
  | TyAppPrec
  | LamPrec
  | ArrowPrec
  | ForallPrec
  | TyLamPrec
  | BlockPrec
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

collectForallVars :: (Show b) => Type b -> ([String], Type b)
collectForallVars (TForall var body) =
  let (vars, finalBody) = collectForallVars body
   in (show var : vars, finalBody)
collectForallVars ty = ([], ty)

prettyType :: (Show b) => Precedence -> Type b -> Doc
prettyType _ (TVar b) = text $ show b
prettyType p (TArrow t1 t2) =
  let s1 = prettyType (succ ArrowPrec) t1
      s2 = prettyType ArrowPrec t2
   in parensIf (p > ArrowPrec) (s1 <+> text "->" <+> s2)
prettyType p ty@(TForall _ _) =
  let (vars, body) = collectForallVars ty
      varsDoc = hsep (map text vars)
      bodyDoc = prettyType ForallPrec body
   in parensIf (p > ForallPrec) (text "forall" <+> varsDoc <+> text "." <+> bodyDoc)
prettyType p (TConstraint traitName typeVars targetType bodyType) =
  let traitDoc = text $ show traitName
      typeVarsDoc = hsep (map (text . show) typeVars)
      targetDoc = prettyType AppPrec targetType
      constraintPart =
        if null typeVars
          then traitDoc <+> targetDoc
          else traitDoc <+> typeVarsDoc <+> targetDoc
      bodyDoc = prettyType ArrowPrec bodyType
   in parensIf (p > ArrowPrec) (constraintPart <+> text "=>" <+> bodyDoc)
prettyType p (TApp t1 t2) =
  let s1 = prettyType AppPrec t1
      s2 = prettyType AtomPrec t2
   in parensIf (p > AppPrec) (s1 <+> s2)
prettyType _ (TList t) =
  let s = prettyType AtomPrec t
   in text "#List" <+> s
prettyType _ TUnit = text "#Unit"

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

fieldDoc :: Ident -> Type Ident -> Doc
fieldDoc f ty = (text (unIdent f) <> text ":") <+> prettyType AtomPrec ty

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
  type BVar Ident = Type Ident
  type BLam Ident = Type Ident
  type BApp Ident = Type Ident
  type BTyApp Ident = Type Ident
  type BLet Ident = Type Ident
  type BBlock Ident = Type Ident
  type BRecord Ident = Type Ident
  type BRecordCreation Ident = Type Ident

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
  | Trait (BTVar b) [(BTVar b, Maybe (Kind (BTVar b)))] [(Ident, Type (BTVar b))]
  | Impl (BTVar b) [BTVar b] (Type (BTVar b)) [(Ident, Expr b)]

isAtomicExpr :: Expr b -> Bool
isAtomicExpr (Var _ _) = True
isAtomicExpr (PrimUnit _) = True
isAtomicExpr (TraitMethod _ _ _ _ _) = True
isAtomicExpr _ = False

needsTypeAnnotation :: Expr Ident -> Bool
needsTypeAnnotation expr = not (isAtomicExpr expr)

prettyStmt :: Stmt Ident -> Doc
prettyStmt (Let letTy b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExprPrec AtomPrec body
      tyDoc = case mty of
        Just t -> text ":" <+> prettyType AtomPrec t
        Nothing -> text ":" <+> prettyType AtomPrec letTy
   in (text "let" <+> (bStr <> tyDoc) <+> text "=" <+> bodyDoc) <> semi
prettyStmt (Type b t) =
  (text "type" <+> text (show b) <+> text "=" <+> prettyType AtomPrec t) <> semi
prettyStmt (Data b fields) =
  let bStr = text $ show b
      fieldsDoc = map (\(f, ty) -> fieldDoc f ty) fields
   in text "data" <+> bStr <+> braces (hsep (punctuate (text ",") fieldsDoc))
prettyStmt (DataForall b vars fields) =
  let bStr = text $ show b
      varsDoc = hsep (map (text . show) vars)
      fieldsDoc = map (\(f, ty) -> fieldDoc f ty) fields
   in text "data"
        <+> bStr
        <+> text "="
        <+> text "forall"
        <+> varsDoc
        <+> text "."
        <+> braces (hsep (punctuate (text ",") fieldsDoc))
prettyStmt (Trait b vars methods) =
  let bStr = text $ show b
      varsDoc = case vars of
        [] -> empty
        vs -> hsep (punctuate (text ",") (map showVar vs))
      showVar (v, mk) = case mk of
        Just k -> text (show v) <+> text ":" <+> prettyKind AtomPrec k
        Nothing -> text (show v)
      methodsDoc = map (\(f, ty) -> fieldDoc f ty) methods
      methodsPart = braces (hsep (punctuate (text ",") methodsDoc))
   in if null vars
        then text "trait" <+> bStr <+> methodsPart
        else text "trait" <+> bStr <+> varsDoc <+> methodsPart
prettyStmt (Impl b vars ty methods) =
  let bStr = text $ show b
      varsDoc = case vars of
        [] -> empty
        vs -> hsep (map (text . show) vs)
      tyDoc = prettyType AtomPrec ty
      methodsDoc = map (\(f, e) -> text (unIdent f) <+> text "=" <+> prettyExprPrec AtomPrec e) methods
      methodsPart = braces (hsep (punctuate (text ",") methodsDoc))
   in if null vars
        then text "instance" <+> bStr <+> text "for" <+> tyDoc <+> methodsPart
        else text "instance" <+> bStr <+> varsDoc <+> text "for" <+> tyDoc <+> methodsPart

prettyExpr :: Expr Ident -> Doc
prettyExpr = prettyExprPrec AtomPrec

prettyExprPrec :: Precedence -> Expr Ident -> Doc
prettyExprPrec _ (Var _ b) = text (show b)
prettyExprPrec p (Lam lamTy b mty body) =
  let bStr = text $ show b
      bodyDoc = prettyExprPrec LamPrec body
      tyDoc = case mty of
        Just t -> text ":" <+> prettyType AtomPrec t
        Nothing -> text ":" <+> prettyType AtomPrec lamTy
   in parensIf (p > LamPrec) (text "\\" <+> (bStr <> tyDoc) <+> text "->" <+> bodyDoc)
prettyExprPrec p (App appTy t1 t2) =
  let s1 = prettyExprPrec AppPrec t1
      s2 = prettyExprPrec AtomPrec t2
      appDoc = s1 <+> s2
   in if needsTypeAnnotation (App appTy t1 t2) && p <= AtomPrec
        then parens (appDoc <+> text ":" <+> prettyType AtomPrec appTy)
        else parensIf (p > AppPrec) appDoc
prettyExprPrec p (TyApp tyAppTy t ty) =
  let s = prettyExprPrec TyAppPrec t
      tyDoc = prettyType AtomPrec ty
      appDoc = s <> (brackets tyDoc)
   in if needsTypeAnnotation (TyApp tyAppTy t ty) && p <= AtomPrec
        then parens (appDoc <+> text ":" <+> prettyType AtomPrec tyAppTy)
        else parensIf (p > TyAppPrec) appDoc
prettyExprPrec p (BlockExpr blockTy block) =
  let blockDoc = prettyBlock block
   in if needsTypeAnnotation (BlockExpr blockTy block) && p <= AtomPrec
        then parens (blockDoc <+> text ":" <+> prettyType AtomPrec blockTy)
        else parensIf (p > BlockPrec) blockDoc
prettyExprPrec p (RecordType recordTy _ fields) =
  let fieldsDoc = map (\(f, ty) -> fieldDoc f ty) fields
      recordDoc = braces (hsep (punctuate (text ",") fieldsDoc))
   in if needsTypeAnnotation (RecordType recordTy undefined fields) && p <= AtomPrec
        then parens (recordDoc <+> text ":" <+> prettyType AtomPrec recordTy)
        else recordDoc
prettyExprPrec p (RecordCreation recordCreationTy expr fields) =
  let exprDoc = prettyExprPrec AtomPrec expr
      fieldsDoc = map (\(f, e) -> text (unIdent f) <+> text "=" <+> prettyExprPrec AtomPrec e) fields
      creationDoc = exprDoc <+> braces (hsep (punctuate (text ",") fieldsDoc))
   in if needsTypeAnnotation (RecordCreation recordCreationTy expr fields) && p <= AtomPrec
        then parens (creationDoc <+> text ":" <+> prettyType AtomPrec recordCreationTy)
        else parensIf (p > AppPrec) creationDoc
prettyExprPrec _ (TraitMethod _ traitName _ targetType methodName) =
  let traitDoc = text (show traitName)
      methodDoc = text (unIdent methodName)
      targetDoc = prettyType AtomPrec targetType
   in traitDoc <> text "." <> methodDoc <> text "@" <> targetDoc
prettyExprPrec _ (PrimUnit _) = text "#Unit"
prettyExprPrec p (PrimNil nilTy ty) =
  let nilDoc = text "#nil" <> (brackets (prettyType AtomPrec ty))
   in if needsTypeAnnotation (PrimNil nilTy ty) && p <= AtomPrec
        then parens (nilDoc <+> text ":" <+> prettyType AtomPrec nilTy)
        else nilDoc
prettyExprPrec p (PrimCons consTy ty headExpr tailExpr) =
  let headDoc = prettyExprPrec AtomPrec headExpr
      tailDoc = prettyExprPrec AtomPrec tailExpr
      consDoc = (text "#cons" <> brackets (prettyType AtomPrec ty)) <+> headDoc <+> tailDoc
   in if needsTypeAnnotation (PrimCons consTy ty headExpr tailExpr) && p <= AtomPrec
        then parens (consDoc <+> text ":" <+> prettyType AtomPrec consTy)
        else parensIf (p > AppPrec) consDoc

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
