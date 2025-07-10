{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.STerm where

import Data.IORef
import Funk.Term
import Funk.Token
import Text.Parsec
import Text.PrettyPrint

data TBinding
  = Bound (Type STBinding)
  | Skolem (Located Ident) Int
  | Unbound SourcePos Int

showTBinding :: TBinding -> IO String
showTBinding (Bound ty) = render <$> prettySType AtomPrec ty
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

prettySType :: Precedence -> SType -> IO Doc
prettySType _ (TVar ref) = do
  b <- readIORef ref
  text <$> showTBinding b
prettySType p (TArrow t1 t2) = do
  s1 <- prettySType ArrowPrec t1
  s2 <- prettySType AtomPrec t2
  return $ parensIf (p > ArrowPrec) (s1 <+> text "->" <+> s2)
prettySType p (TForall ref t) = do
  b <- readIORef ref
  bStr <- text <$> showTBinding b
  st <- prettySType ForallPrec t
  return $ parensIf (p > ForallPrec) (text "\\/" <+> bStr <+> text "." <+> st)
prettySType p (TLam ref t) = do
  b <- readIORef ref
  bStr <- text <$> showTBinding b
  tStr <- prettySType LamPrec t
  return $ parensIf (p > LamPrec) (text "/\\" <+> bStr <+> text "." <+> tStr)

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
  {
    sLamInput :: STBinding,
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

data Precedence = AtomPrec | AppPrec | LamPrec | TyAppPrec | TyLamPrec | BlockPrec | ArrowPrec | ForallPrec
  deriving (Eq, Ord)

showSExpr :: SExpr -> IO String
showSExpr = fmap render . prettySExpr AtomPrec

prettySExpr :: Precedence -> SExpr -> IO Doc
prettySExpr p (Var _ ref) = do
  v <- readIORef (unSBinding ref)
  case v of
    VBound t -> prettySExpr p t
    VUnbound i -> return $ text (unIdent (unLocated i))
prettySExpr p (Lam ty ref _ body) = do
  v <- readIORef (unSBinding ref)
  bodyDoc <- prettySExpr LamPrec body
  tyBinding <- readIORef $ sLamInput ty
  tyDoc <- text <$> showTBinding tyBinding
  let doc = case v of
        VBound t -> do
          tDoc <- prettySExpr AtomPrec t
          return $ text "\\" <+> tDoc <+> text ":" <+> tyDoc <+> text "." <+> bodyDoc
        VUnbound i ->
          return $ text "\\" <+> text (unIdent (unLocated i)) <+> text ":" <+> tyDoc <+> text "." <+> bodyDoc
  parensIf (p > LamPrec) <$> doc
prettySExpr p (App _ t1 t2) = do
  s1 <- prettySExpr AppPrec t1
  s2 <- prettySExpr AtomPrec t2
  return $ parensIf (p > AppPrec) (s1 <+> s2)
prettySExpr p (TyApp _ t ty) = do
  s <- prettySExpr TyAppPrec t
  tyDoc <- prettySType AtomPrec ty
  return $ parensIf (p > TyAppPrec) (s <+> brackets tyDoc)
prettySExpr p (TyLam _ ref body) = do
  v <- readIORef ref
  bodyDoc <- prettySExpr TyLamPrec body
  let doc = case v of
        Bound t -> do
          tDoc <- prettySType AtomPrec t
          return $ text "/\\" <+> tDoc <+> text "." <+> bodyDoc
        Skolem i _ ->
          return $ text "/\\" <+> text (unIdent (unLocated i)) <+> text "." <+> bodyDoc
        Unbound _ idx ->
          return $ text "/\\" <+> text ("_" ++ show idx) <+> text "." <+> bodyDoc
  parensIf (p > TyLamPrec) <$> doc

prettySExpr p (BlockExpr _ block) = do
  blockDoc <- prettySBlock block
  return $ parensIf (p > BlockPrec) blockDoc

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

showSStmt :: SStmt -> IO String
showSStmt = fmap render . prettySStmt

prettySStmt :: SStmt -> IO Doc
prettySStmt (Let _ ref _ body) = do
  v <- readIORef (unSBinding ref)
  bodyDoc <- prettySExpr AtomPrec body
  case v of
    VBound t -> do
      tDoc <- prettySExpr AtomPrec t
      return $ tDoc <+> text "=" <+> bodyDoc Text.PrettyPrint.<> semi
    VUnbound i ->
      return $ text (unIdent (unLocated i)) <+> text "=" <+> bodyDoc Text.PrettyPrint.<> semi
prettySStmt (Type sbinding ty) = do
  sbindingVal <- readIORef sbinding
  vStr <- showTBinding sbindingVal
  tyDoc <- prettySType AtomPrec ty
  return $ text "type" <+> text vStr <+> text "=" <+> tyDoc Text.PrettyPrint.<> semi

showSBlock :: SBlock -> IO String
showSBlock = fmap render . prettySBlock

prettySBlock :: SBlock -> IO Doc
prettySBlock (Block stmts expr) = do
  stmtsDocs <- mapM prettySStmt stmts
  exprDoc <- prettySExpr AtomPrec expr
  return $ vcat stmtsDocs Text.PrettyPrint.$+$ (exprDoc Text.PrettyPrint.<> semi)