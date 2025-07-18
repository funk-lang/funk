{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.Subst where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Parser
import Funk.STerm
import Funk.Term
import Funk.Token
import Text.Parsec
import qualified Text.Parsec.Pos as Pos

-- Find a trait method by name in the trait definitions
findTraitMethod :: String -> Map Ident SStmt -> Maybe (Ident, STBinding)
findTraitMethod methodName traits =
  case [ (traitName, traitRef) | (traitName, Trait traitRef _ methods) <- Map.toList traits, any (\(method, _) -> unIdent method == methodName) methods
       ] of
    (traitName, traitRef) : _ -> Just (traitName, traitRef)
    [] -> Nothing

data Env
  = Env
  { envVars :: Map Ident SBinding,
    envTys :: Map Ident STBinding,
    envVarTypes :: Map Ident STBinding,
    envTraits :: Map Ident SStmt, -- trait definitions
    envImpls :: [(STBinding, [STBinding], SType, SStmt)], -- impl instances
    envNextIdx :: Int
  }

emptyEnv :: Env
emptyEnv = Env {envVars = Map.empty, envTys = Map.empty, envVarTypes = Map.empty, envTraits = Map.empty, envImpls = [], envNextIdx = 0}

newtype Subst a = Subst {unSubst :: ExceptT [Located Ident] (StateT Env IO) a}
  deriving (Functor, Monad, MonadIO, MonadState Env, MonadError [Located Ident])

instance Applicative Subst where
  pure = Subst . pure
  Subst f <*> Subst x = Subst $ do
    f' <- catchError (Right <$> f) (return . Left)
    x' <- catchError (Right <$> x) (return . Left)
    case (f', x') of
      (Right fVal, Right xVal) -> return (fVal xVal)
      (Left errs1, Left errs2) -> throwError (errs1 ++ errs2)
      (Left errs, _) -> throwError errs
      (_, Left errs) -> throwError errs

runSubst :: Subst a -> IO (Either [Located Ident] a, Env)
runSubst solver = runStateT (runExceptT $ unSubst solver) emptyEnv

freshSkolem :: Located Ident -> Subst STBinding
freshSkolem i = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO . newIORef $ Skolem i idx
  put
    env
      { envTys = Map.insert (unLocated i) ref $ envTys env,
        envNextIdx = envNextIdx env + 1
      }
  return ref

freshUnboundTy :: SourcePos -> Subst STBinding
freshUnboundTy pos = do
  env <- get
  let idx = envNextIdx env
  ref <- liftIO $ newIORef (Unbound pos idx)
  put env {envNextIdx = envNextIdx env + 1}
  return ref

substTy :: PType -> Subst SType
substTy pty = case pty of
  TVar i -> do
    env <- get
    case Map.lookup (unLocated i) (envTys env) of
      Just ref -> return $ TVar ref
      Nothing -> throwError [i]
  TArrow t1 t2 -> TArrow <$> substTy t1 <*> substTy t2
  TForall i t -> do
    ref <- freshSkolem i
    st <- substTy t
    return $ TForall ref st
  TConstraint traitName typeVars targetType bodyType -> do
    traitName' <- freshSkolem traitName
    typeVars' <- mapM freshSkolem typeVars
    targetType' <- substTy targetType
    bodyType' <- substTy bodyType
    return $ TConstraint traitName' typeVars' targetType' bodyType'
  TApp t1 t2 -> TApp <$> substTy t1 <*> substTy t2
  TList t -> TList <$> substTy t
  TIO t -> TIO <$> substTy t
  TUnit -> return TUnit
  TString -> return TString
  TInt -> return TInt
  TBool -> return TBool

extractPBinding :: PExpr -> PBinding
extractPBinding (Var _ pbinding) = pbinding
extractPBinding _ = error "Expected Var for record creation"

substExpr :: PExpr -> Subst SExpr
substExpr pexpr = case pexpr of
  Var _ (PBinding i) -> do
    env <- get
    let methodName = unLocated i

    -- Check if this is a trait method by looking for it in trait definitions
    case findTraitMethod (unIdent methodName) (envTraits env) of
      Just (_, traitRef) -> do
        -- Generate a TraitMethod call
        let pos = locatedPos i
        targetTy <- freshUnboundTy pos
        iTy <- freshUnboundTy pos
        return $ TraitMethod iTy traitRef [] (TVar targetTy) methodName
      Nothing -> do
        -- Regular variable lookup
        termBinding <- case Map.lookup (unLocated i) (envVars env) of
          Just ref -> return ref
          Nothing -> throwError [i]
        typeBinding <- case Map.lookup (unLocated i) (envVarTypes env) of
          Just ty -> return ty
          Nothing -> throwError [i]
        return $ Var typeBinding termBinding
  QualifiedVar _ _modPath (PBinding _i) -> do
    -- For now, treat qualified variables as errors since module resolution isn't implemented
    error "QualifiedVar not yet implemented in substitution"
  Lam pos (PBinding i) mty body -> do
    i' <- liftIO $ newIORef (VUnbound i)
    iTy <- freshUnboundTy pos
    modify $ \env ->
      env
        { envVars = Map.insert (unLocated i) (SBinding i') (envVars env),
          envVarTypes = Map.insert (unLocated i) iTy (envVarTypes env)
        }
    tyAnn <- case mty of
      Just ty -> Just <$> substTy ty
      Nothing -> return Nothing
    body' <- substExpr body
    oTy <- freshUnboundTy pos
    return $ Lam (SLam iTy oTy) (SBinding i') tyAnn body'
  App pos t1 t2 -> App <$> freshUnboundTy pos <*> substExpr t1 <*> substExpr t2
  TyApp pos t ty -> TyApp <$> freshUnboundTy pos <*> substExpr t <*> substTy ty
  BlockExpr pos block -> BlockExpr <$> freshUnboundTy pos <*> substBlock block
  RecordType () (PBinding i) fields -> do
    sfields <- forM fields $ \(f, ty) -> do
      sty <- substTy ty
      return (f, sty)
    i' <- liftIO $ newIORef (VUnbound i)
    iTy <- freshUnboundTy (locatedPos i)
    modify $ \env ->
      env
        { envVars = Map.insert (unLocated i) (SBinding i') (envVars env),
          envVarTypes = Map.insert (unLocated i) iTy (envVarTypes env)
        }
    return $ RecordType iTy (SBinding i') sfields
  RecordCreation _ v fields -> do
    sfields <- forM fields $ \(f, e) -> do
      sexpr <- substExpr e
      return (f, sexpr)
    sexpr <- substExpr v
    -- Look up the constructor type in the environment instead of creating fresh unbound type
    let constructorName = unLocated (unPBinding (extractPBinding v))
    env <- get
    iTy <- case Map.lookup constructorName (envVarTypes env) of
      Just existingType -> return existingType
      Nothing -> freshUnboundTy (locatedPos (unPBinding (extractPBinding v)))
    return $ RecordCreation iTy sexpr sfields
  TraitMethod pos traitName typeArgs targetType methodName -> do
    env <- get
    traitRef <- case Map.lookup (unLocated traitName) (envTys env) of
      Just ref -> return ref
      Nothing -> throwError [traitName]
    typeArgs' <- mapM substTy typeArgs
    -- For placeholder types, create a fresh unbound type
    targetType' <-
      if show (getTVarName targetType) == "PlaceholderType"
        then TVar <$> freshUnboundTy pos
        else substTy targetType
    iTy <- freshUnboundTy pos
    return $ TraitMethod iTy traitRef typeArgs' targetType' methodName
  PrimUnit _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimUnit iTy
  PrimString _ s -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimString iTy s
  PrimInt _ i -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimInt iTy i
  PrimTrue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimTrue iTy
  PrimFalse _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimFalse iTy
  PrimNil _ ty -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    ty' <- substTy ty
    return $ PrimNil iTy ty'
  PrimCons _ ty headExpr tailExpr -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    ty' <- substTy ty
    head' <- substExpr headExpr
    tail' <- substExpr tailExpr
    return $ PrimCons iTy ty' head' tail'
  PrimPrint _ e -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e' <- substExpr e
    return $ PrimPrint iTy e'
  PrimPureIO _ e -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e' <- substExpr e
    return $ PrimPureIO iTy e'


  PrimApplyIO _ iof iox -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    iof' <- substExpr iof
    iox' <- substExpr iox
    return $ PrimApplyIO iTy iof' iox'
  PrimFmapIO _ f io -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    f' <- substExpr f
    io' <- substExpr io
    return $ PrimFmapIO iTy f' io'
  PrimBindIO _ iox f -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    iox' <- substExpr iox
    f' <- substExpr f
    return $ PrimBindIO iTy iox' f'
  PrimIntEq _ e1 e2 -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e1' <- substExpr e1
    e2' <- substExpr e2
    return $ PrimIntEq iTy e1' e2'
  PrimStringEq _ e1 e2 -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e1' <- substExpr e1
    e2' <- substExpr e2
    return $ PrimStringEq iTy e1' e2'
  PrimIfThenElse _ c t e -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    c' <- substExpr c
    t' <- substExpr t
    e' <- substExpr e
    return $ PrimIfThenElse iTy c' t' e'
  PrimIntSub _ e1 e2 -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e1' <- substExpr e1
    e2' <- substExpr e2
    return $ PrimIntSub iTy e1' e2'
  PrimExit _ e -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e' <- substExpr e
    return $ PrimExit iTy e'
  PrimStringConcat _ e1 e2 -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    e1' <- substExpr e1
    e2' <- substExpr e2
    return $ PrimStringConcat iTy e1' e2'
  -- Primitive values (for currying)
  PrimFmapIOValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimFmapIOValue iTy
  PrimPureIOValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimPureIOValue iTy
  PrimApplyIOValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimApplyIOValue iTy
  PrimBindIOValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimBindIOValue iTy
  PrimIntEqValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimIntEqValue iTy
  PrimStringEqValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimStringEqValue iTy
  PrimStringConcatValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimStringConcatValue iTy
  PrimIfThenElseValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimIfThenElseValue iTy
  PrimIntSubValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimIntSubValue iTy
  PrimExitValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimExitValue iTy
  PrimPrintValue _ -> do
    iTy <- freshUnboundTy (Pos.newPos "" 1 1)
    return $ PrimPrintValue iTy
  where
    getTVarName (TVar ident) = unLocated ident
    getTVarName _ = Ident "other"

substStmt :: PStmt -> Subst SStmt
substStmt (Let () (PBinding i) mty body) = do
  i' <- liftIO $ newIORef (VUnbound i)
  iTy <- freshUnboundTy (locatedPos i)
  modify $ \env ->
    env
      { envVars = Map.insert (unLocated i) (SBinding i') (envVars env),
        envVarTypes = Map.insert (unLocated i) iTy (envVarTypes env)
      }
  tyAnn <- case mty of
    Just ty -> Just <$> substTy ty
    Nothing -> return Nothing
  body' <- substExpr body
  return $ Let iTy (SBinding i') tyAnn body'
substStmt (Type i pty) = do
  sty <- substTy pty
  ref <- freshSkolem i
  return $ Type ref sty
substStmt (Data i fields) = do
  sfields <- forM fields $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  vRef <- liftIO $ newIORef (VUnbound i)
  modify $ \env ->
    env
      { envVars = Map.insert (unLocated i) (SBinding vRef) (envVars env),
        envVarTypes = Map.insert (unLocated i) ref (envVarTypes env)
      }
  
  -- Add field accessors to the environment
  forM_ fields $ \(fieldIdent, _fieldTy) -> do
    fieldRef <- liftIO $ newIORef (VUnbound (Located (locatedPos i) fieldIdent))
    -- Field accessor type: create fresh unbound type for now
    fieldAccessorTy <- freshUnboundTy (locatedPos i)
    modify $ \env ->
      env
        { envVars = Map.insert fieldIdent (SBinding fieldRef) (envVars env),
          envVarTypes = Map.insert fieldIdent fieldAccessorTy (envVarTypes env)
        }
  
  return $ Data ref sfields
substStmt (DataForall i vars fields) = do
  vars' <- mapM freshSkolem vars
  sfields <- forM fields $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  vRef <- liftIO $ newIORef (VUnbound i)
  modify $ \env ->
    env
      { envVars = Map.insert (unLocated i) (SBinding vRef) (envVars env),
        envVarTypes = Map.insert (unLocated i) ref (envVarTypes env)
      }
  
  -- Add field accessors to the environment
  forM_ fields $ \(fieldIdent, _fieldTy) -> do
    fieldRef <- liftIO $ newIORef (VUnbound (Located (locatedPos i) fieldIdent))
    -- Field accessor type: create fresh unbound type for now
    fieldAccessorTy <- freshUnboundTy (locatedPos i)
    modify $ \env ->
      env
        { envVars = Map.insert fieldIdent (SBinding fieldRef) (envVars env),
          envVarTypes = Map.insert fieldIdent fieldAccessorTy (envVarTypes env)
        }
  
  return $ DataForall ref vars' sfields
substStmt (Trait i vars methods) = do
  vars' <- mapM freshSkolem vars
  smethods <- forM methods $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  let traitStmt' = Trait ref vars' smethods
  modify $ \env -> env {envTraits = Map.insert (unLocated i) traitStmt' (envTraits env)}
  return traitStmt'
substStmt (TraitWithKinds i vars methods) = do
  vars' <- mapM (freshSkolem . fst) vars
  smethods <- forM methods $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  let traitStmt' = Trait ref vars' smethods
  modify $ \env -> env {envTraits = Map.insert (unLocated i) traitStmt' (envTraits env)}
  return traitStmt'
substStmt (Impl i vars ty methods) = do
  vars' <- mapM freshSkolem vars
  sty <- substTy ty
  smethods <- forM methods $ \(f, e) -> do
    sexpr <- substExpr e
    return (f, sexpr)
  ref <- freshSkolem i
  let implStmt' = Impl ref vars' sty smethods
  modify $ \env -> env {envImpls = (ref, vars', sty, implStmt') : envImpls env}
  return implStmt'
substStmt (PubLet () (PBinding i) mty body) = do
  i' <- liftIO $ newIORef (VUnbound i)
  iTy <- freshUnboundTy (locatedPos i)
  modify $ \env ->
    env
      { envVars = Map.insert (unLocated i) (SBinding i') (envVars env),
        envVarTypes = Map.insert (unLocated i) iTy (envVarTypes env)
      }
  tyAnn <- case mty of
    Just ty -> Just <$> substTy ty
    Nothing -> return Nothing
  body' <- substExpr body
  return $ PubLet iTy (SBinding i') tyAnn body'
substStmt (PubType i pty) = do
  sty <- substTy pty
  ref <- freshSkolem i
  return $ PubType ref sty
substStmt (PubData i fields) = do
  sfields <- forM fields $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  vRef <- liftIO $ newIORef (VUnbound i)
  modify $ \env ->
    env
      { envVars = Map.insert (unLocated i) (SBinding vRef) (envVars env),
        envVarTypes = Map.insert (unLocated i) ref (envVarTypes env)
      }
  
  -- Add field accessors to the environment
  forM_ fields $ \(fieldIdent, _fieldTy) -> do
    fieldRef <- liftIO $ newIORef (VUnbound (Located (locatedPos i) fieldIdent))
    -- Field accessor type: create fresh unbound type for now
    fieldAccessorTy <- freshUnboundTy (locatedPos i)
    modify $ \env ->
      env
        { envVars = Map.insert fieldIdent (SBinding fieldRef) (envVars env),
          envVarTypes = Map.insert fieldIdent fieldAccessorTy (envVarTypes env)
        }
  
  return $ PubData ref sfields
substStmt (PubDataForall i vars fields) = do
  vars' <- mapM freshSkolem vars
  sfields <- forM fields $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  return $ PubDataForall ref vars' sfields
substStmt (PubTrait i vars methods) = do
  vars' <- mapM freshSkolem vars
  smethods <- forM methods $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  return $ PubTrait ref vars' smethods
substStmt (PubTraitWithKinds i vars methods) = do
  vars' <- mapM (freshSkolem . fst) vars
  smethods <- forM methods $ \(f, ty) -> do
    sty <- substTy ty
    return (f, sty)
  ref <- freshSkolem i
  let traitStmt' = PubTrait ref vars' smethods
  modify $ \env -> env {envTraits = Map.insert (unLocated i) traitStmt' (envTraits env)}
  return traitStmt'
substStmt (Use _modPath _items) = do
  -- For now, ignore use statements during substitution
  -- TODO: Implement proper module system
  return $ Use _modPath _items
substStmt (PubUse _modPath _items) = do
  -- For now, ignore pub use statements during substitution  
  -- TODO: Implement proper module system
  return $ PubUse _modPath _items
substStmt (UseAll _modPath) = do
  -- For now, ignore use all statements during substitution
  -- TODO: Implement proper module system
  return $ UseAll _modPath
substStmt (PubUseAll _modPath) = do
  -- For now, ignore pub use all statements during substitution
  -- TODO: Implement proper module system
  return $ PubUseAll _modPath

substBlock :: PBlock -> Subst SBlock
substBlock (Block stmts e) = Block <$> mapM substStmt stmts <*> substExpr e
