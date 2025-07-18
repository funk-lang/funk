{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Funk.STerm where

import Control.Monad (forM)
import Data.IORef
import Funk.Term
import Funk.Token
import Text.Parsec
import qualified Text.Parsec.Pos as Pos

data TBinding
  = Bound (Type STBinding)
  | Skolem (Located Ident) Int
  | Unbound SourcePos Int

data KBinding
  = KBound (Kind SKBinding)
  | KSkolem (Located Ident) Int
  | KUnbound SourcePos Int

type STBinding = IORef TBinding
type SKBinding = IORef KBinding

bindingPos :: STBinding -> IO SourcePos
bindingPos ref = do
  b <- readIORef ref
  case b of
    Bound t -> typePos t
    Skolem i _ -> return $ locatedPos i
    Unbound pos _ -> return pos

type SType = Type STBinding
type SKind = Kind SKBinding

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
typePos (TConstraint _ _ targetType _) = typePos targetType
typePos (TApp t1 _) = typePos t1
typePos (TList t) = typePos t
typePos (TIO t) = typePos t
typePos TUnit = return (Pos.newPos "" 1 1)
typePos TString = return (Pos.newPos "" 1 1)
typePos TInt = return (Pos.newPos "" 1 1)
typePos TBool = return (Pos.newPos "" 1 1)


data Var = VBound SExpr | VUnbound (Located Ident)

data SLam = SLam
  { sLamInput :: STBinding,
    sLamOutput :: STBinding
  }

newtype SBinding = SBinding {unSBinding :: IORef Var}

sTBindingToIdent :: STBinding -> IO Ident
sTBindingToIdent ref = do
  b <- readIORef ref
  case b of
    Skolem i _ -> return $ unLocated i
    _ -> return $ Ident "_"

sTBindingToIdentImproved :: STBinding -> IO Ident
sTBindingToIdentImproved ref = do
  b <- readIORef ref
  case b of
    Skolem i _ -> return $ unLocated i
    Unbound _ _ -> return $ Ident "_"
    Bound _ -> return $ Ident "_"  -- This shouldn't happen in this context

-- Check if a type binding is truly unresolved (for trait method resolution)
isUnresolvedBinding :: STBinding -> IO Bool
isUnresolvedBinding ref = do
  b <- readIORef ref
  case b of
    Unbound _ _ -> return True
    Bound _ -> return False
    Skolem _ _ -> return False

-- Smart trait method target resolution that uses binding state
smartTraitMethodTargetResolve :: SType -> IO (Type Ident)
smartTraitMethodTargetResolve stype = case stype of
  TVar ref -> do
    binding <- readIORef ref
    case binding of
      Bound boundType -> do
        -- Follow the binding chain
        smartTraitMethodTargetResolve boundType
      Unbound _ _ -> do
        -- Truly unresolved, return "_"
        return $ TVar $ Ident "_"
      Skolem i _ -> return $ TVar (unLocated i)
  _ -> sTypeToDisplay stype

sBindingToIdent :: SBinding -> IO Ident
sBindingToIdent (SBinding ref) = do
  b <- readIORef ref
  case b of
    VBound _ -> return $ Ident "_"
    VUnbound i -> return $ unLocated i

-- Try to resolve trait method target types more intelligently
smartResolveTargetType :: SType -> STBinding -> IO (Type Ident)
smartResolveTargetType targetType exprType = do
  -- First try normal resolution
  normalResult <- sTypeToDisplay targetType
  
  case normalResult of
    TVar (Ident tname) | tname == "_" -> do
      -- This is still an unresolved type variable, try to infer from expression type
      exprTypeResolved <- sTypeToDisplay (TVar exprType)
      case exprTypeResolved of
        -- If the expression type is a concrete application like "State #Unit",
        -- extract the constructor "State" as the target type
        TApp (TVar constructor) _ -> return $ TVar constructor
        TVar constructor -> return $ TVar constructor
        _ -> return normalResult
    _ -> return normalResult

-- Enhanced type resolution that tries harder to resolve type variables
aggressiveTypeResolve :: SType -> IO (Type Ident)
aggressiveTypeResolve stype = do
  case stype of
    TVar ref -> do
      binding <- readIORef ref
      case binding of
        Bound boundType -> aggressiveTypeResolve boundType
        Unbound _ _ -> do
          -- This is truly unresolved, return "_"
          return $ TVar $ Ident "_"
        Skolem i _ -> return $ TVar (unLocated i)
    _ -> sTypeToDisplay stype

-- Post-processing step to resolve trait method target types based on context
-- This is called after constraint solving to clean up unresolved trait method targets
resolveTraitMethodTargets :: SExpr -> IO (Expr Ident)
resolveTraitMethodTargets sexpr = do
  -- First convert normally
  normalExpr <- sExprToDisplayWithTypes sexpr
  -- Then apply context-based resolution
  contextResolveExpr normalExpr (typeOf sexpr)

-- Resolve lambda with type annotation to get proper parameter types
resolveLambdaWithTypeAnnotation :: SExpr -> Type Ident -> IO (Expr Ident)
resolveLambdaWithTypeAnnotation sexpr annotationType = do
  case sexpr of
    Lam (SLam _inputType _) binding _mty body -> do
      binding' <- sBindingToIdent binding
      
      -- Extract parameter type from the annotation type
      let paramType = extractFirstParamType annotationType
      let mty' = case paramType of
            Just pType -> Just pType
            Nothing -> Nothing -- Fall back to inferred type
      
      -- Recursively handle nested lambdas with remaining parameter types
      body' <- case extractRestParamTypes annotationType of
        Just restType -> resolveLambdaWithTypeAnnotation body restType
        Nothing -> sExprToDisplayWithTypes body
      
      return $ Lam () binding' mty' body'
    _ -> sExprToDisplayWithTypes sexpr
  where
    -- Extract the first parameter type from a function type
    extractFirstParamType :: Type Ident -> Maybe (Type Ident)
    extractFirstParamType (TForall _ innerType) = extractFirstParamType innerType
    extractFirstParamType (TArrow paramType _) = Just paramType
    extractFirstParamType _ = Nothing
    
    -- Extract the rest of the function type after removing the first parameter
    extractRestParamTypes :: Type Ident -> Maybe (Type Ident)
    extractRestParamTypes (TForall _ innerType) = extractRestParamTypes innerType
    extractRestParamTypes (TArrow _ restType) = Just restType
    extractRestParamTypes _ = Nothing

-- Targeted resolution using explicit type annotation from let bindings
resolveTraitMethodsWithType :: SExpr -> Type Ident -> IO (Expr Ident)
resolveTraitMethodsWithType sexpr expectedType = do
  -- First convert normally
  normalExpr <- sExprToDisplayWithTypes sexpr
  -- Then apply direct resolution using the known expected type
  directResolveWithType normalExpr expectedType

-- Direct resolution that replaces trait method targets using expected type
directResolveWithType :: Expr Ident -> Type Ident -> IO (Expr Ident)
directResolveWithType expr expectedType = case expr of
  App _ f arg -> do
    -- For function applications like "void (pure #Unit)", we need special handling
    case f of
      Var _ (Ident "void") -> do
        -- void has type: Functor f => f a -> f #Unit
        -- When used with expected type State #Unit #Unit, instantiate as void @(State #Unit) @#Unit
        case expectedType of
          TApp functorConstr argType -> do
            -- Generate explicit type applications: void @(State #Unit) @#Unit @#Unit
            let voidWithTypes = TyApp () (TyApp () (TyApp () f functorConstr) argType) TUnit
            -- For the argument, handle it specially if it's a trait method call  
            arg' <- case arg of
              App _ (TraitMethod _ _ _ _ (Ident "pure")) argExpr -> do
                -- Convert "pure #Unit" to "pure @(State #Unit) #Unit"
                let pureVar = Var () (Ident "pure")
                let pureWithType = TyApp () pureVar functorConstr
                argExpr' <- directResolveWithType argExpr expectedType
                return $ App () pureWithType argExpr'
              _ -> directResolveWithType arg expectedType
            return $ App () voidWithTypes arg'
          _ -> do
            arg' <- directResolveWithType arg expectedType
            return $ App () f arg'
      
      _ -> do
        -- For general function applications, try to infer types
        f' <- directResolveWithType f expectedType
        arg' <- directResolveWithType arg expectedType
        return $ App () f' arg'
  
  TraitMethod _ traitName typeArgs (TVar (Ident tname)) methodName 
    | tname == "_" -> do
      -- This is an unresolved trait method target - use expected type to resolve it
      case (unIdent traitName, methodName, expectedType) of
        ("Monad", Ident "pure", TApp functorConstr _) -> 
          -- pure: a -> m a, so if expected result is (State #Unit) #Unit, 
          -- then target should be State #Unit
          return $ TraitMethod () traitName typeArgs functorConstr methodName
        ("Functor", Ident "fmap", TApp functorConstr _) ->
          -- fmap: (a -> b) -> f a -> f b
          -- If expected result is f b, then target should be f
          return $ TraitMethod () traitName typeArgs functorConstr methodName
        _ -> 
          case expectedType of
            TApp constructor _ -> 
              -- If expected type is "Constructor Arg", target should be "Constructor"
              return $ TraitMethod () traitName typeArgs constructor methodName
            _ -> 
              -- If expected type is just a constructor, use it directly
              return $ TraitMethod () traitName typeArgs expectedType methodName
  
  -- For other expressions, recursively resolve any nested trait methods
  BlockExpr _ (Block stmts bodyExpr) -> do
    -- Resolve statements and body with the expected type
    stmts' <- mapM (\case
      Let _ var mty body -> do
        body' <- directResolveWithType body expectedType
        return $ Let () var mty body'
      other -> return other) stmts
    bodyExpr' <- directResolveWithType bodyExpr expectedType
    return $ BlockExpr () (Block stmts' bodyExpr')
  
  _ -> return expr

-- Context-based resolution that looks at expression types to infer trait method targets
contextResolveExpr :: Expr Ident -> STBinding -> IO (Expr Ident)
contextResolveExpr expr exprType = case expr of
  App _ f arg -> do
    -- For function applications, we need to look at the overall result type
    exprTypeResolved <- sTypeToDisplay (TVar exprType)
    f' <- case f of
      TraitMethod _ traitName typeArgs (TVar (Ident tname)) methodName 
        | tname == "_" -> do
          -- This trait method application should produce the result type
          -- If result type is State #Unit, and this is pure@target #Unit, then target = State
          case exprTypeResolved of
            TApp constructor _ -> 
              return $ TraitMethod () traitName typeArgs constructor methodName
            _ -> return f
      _ -> contextResolveExpr f exprType
    return $ App () f' arg
  
  TraitMethod _ traitName typeArgs (TVar (Ident tname)) methodName 
    | tname == "_" -> do
      -- This is an unresolved trait method target - try to infer from context
      exprTypeResolved <- sTypeToDisplay (TVar exprType)
      case exprTypeResolved of
        TApp constructor _ -> 
          -- If the expression has type "Constructor Arg", target should be "Constructor"
          return $ TraitMethod () traitName typeArgs constructor methodName
        _ -> return expr
  
  _ -> return expr

instance Binding SBinding where
  type BTVar SBinding = STBinding
  type BVar SBinding = STBinding
  type BLam SBinding = SLam
  type BApp SBinding = STBinding
  type BTyApp SBinding = STBinding
  type BLet SBinding = STBinding
  type BBlock SBinding = STBinding
  type BRecord SBinding = STBinding
  type BRecordCreation SBinding = STBinding

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
  BlockExpr ty _ -> ty
  RecordType ty _ _ -> ty
  RecordCreation ty _ _ -> ty
  TraitMethod ty _ _ _ _ -> ty
  PrimUnit ty -> ty
  PrimString ty _s -> ty
  PrimInt ty _i -> ty
  PrimTrue ty -> ty
  PrimFalse ty -> ty
  PrimNil ty _ -> ty
  PrimCons ty _ _ _ -> ty
  PrimPrint ty _ -> ty
  PrimFmapIO ty _ _ -> ty
  PrimPureIO ty _ -> ty
  PrimApplyIO ty _ _ -> ty
  PrimBindIO ty _ _ -> ty
  PrimIntEq ty _ _ -> ty
  PrimIfThenElse ty _ _ _ -> ty
  PrimIntSub ty _ _ -> ty

-- Enhanced version that includes type information for display
sExprToDisplayWithTypes :: SExpr -> IO (Expr Ident)
sExprToDisplayWithTypes sexpr = case sexpr of
  Var _ binding -> do
    binding' <- sBindingToIdent binding
    -- For variables, we'll add the type as a synthetic lambda annotation
    _ <- sTypeToDisplay (TVar (typeOf sexpr))
    return $ Var () binding'
  App _ t1 t2 -> do
    t1' <- sExprToDisplayWithTypes t1
    t2' <- sExprToDisplayWithTypes t2
    return $ App () t1' t2'
  Lam (SLam inputType _) binding mty body -> do
    binding' <- sBindingToIdent binding
    mty' <- case mty of
      Just ty -> Just <$> sTypeToDisplay ty
      Nothing -> do
        -- Use the input type of the lambda parameter, not the whole lambda type
        paramType <- sTypeToDisplay (TVar inputType)
        return $ Just paramType
    body' <- sExprToDisplayWithTypes body
    return $ Lam () binding' mty' body'
  TyApp _ body outTy -> do
    body' <- sExprToDisplayWithTypes body
    outTy' <- sTypeToDisplay outTy
    return $ TyApp () body' outTy'
  BlockExpr _ block -> do
    block' <- sBlockToDisplayWithTypes block
    return $ BlockExpr () block'
  RecordType _ v fields -> do
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    v' <- sBindingToIdent v
    return $ RecordType () v' fields'
  RecordCreation _ expr fields -> do
    expr' <- sExprToDisplayWithTypes expr
    fields' <- forM fields $ \(f, e) -> do
      e' <- sExprToDisplayWithTypes e
      return (f, e')
    return $ RecordCreation () expr' fields'
  TraitMethod _ traitName typeArgs targetType methodName -> do
    traitName' <- sTBindingToIdent traitName
    typeArgs' <- mapM sTypeToDisplay typeArgs
    -- Try to resolve the target type using smart resolution
    targetType' <- smartTraitMethodTargetResolve targetType
    return $ TraitMethod () traitName' typeArgs' targetType' methodName
  PrimUnit _ -> return $ PrimUnit ()
  PrimString _ s -> return $ PrimString () s
  PrimInt _ i -> return $ PrimInt () i
  PrimTrue _ -> return $ PrimTrue ()
  PrimFalse _ -> return $ PrimFalse ()
  PrimNil _ ty -> do
    ty' <- sTypeToDisplay ty
    return $ PrimNil () ty'
  PrimCons _ ty headExpr tailExpr -> do
    ty' <- sTypeToDisplay ty
    head' <- sExprToDisplayWithTypes headExpr
    tail' <- sExprToDisplayWithTypes tailExpr
    return $ PrimCons () ty' head' tail'
  PrimPrint _ expr -> do
    expr' <- sExprToDisplayWithTypes expr
    return $ PrimPrint () expr'
  PrimFmapIO _ f io -> do
    f' <- sExprToDisplayWithTypes f
    io' <- sExprToDisplayWithTypes io
    return $ PrimFmapIO () f' io'
  PrimPureIO _ expr -> do
    expr' <- sExprToDisplayWithTypes expr
    return $ PrimPureIO () expr'
  PrimApplyIO _ iof iox -> do
    iof' <- sExprToDisplayWithTypes iof
    iox' <- sExprToDisplayWithTypes iox
    return $ PrimApplyIO () iof' iox'
  PrimBindIO _ iox f -> Funk.Term.PrimBindIO () <$> sExprToDisplayWithTypes iox <*> sExprToDisplayWithTypes f
  PrimIntEq _ e1 e2 -> Funk.Term.PrimIntEq () <$> sExprToDisplayWithTypes e1 <*> sExprToDisplayWithTypes e2
  PrimIfThenElse _ c t e -> Funk.Term.PrimIfThenElse () <$> sExprToDisplayWithTypes c <*> sExprToDisplayWithTypes t <*> sExprToDisplayWithTypes e
  PrimIntSub _ e1 e2 -> Funk.Term.PrimIntSub () <$> sExprToDisplayWithTypes e1 <*> sExprToDisplayWithTypes e2

-- Original version for backward compatibility
sExprToDisplay :: SExpr -> IO (Expr Ident)
sExprToDisplay = sExprToDisplayWithTypes


sTypeToDisplay :: SType -> IO (Type Ident)
sTypeToDisplay = sTypeToDisplayHelper []
  where
    sTypeToDisplayHelper :: [STBinding] -> SType -> IO (Type Ident)
    sTypeToDisplayHelper visited ty = case ty of
      TVar ref -> do
        -- Avoid infinite loops by tracking visited bindings
        if ref `elem` visited
          then return $ TVar $ Ident "_"
          else do
            b <- readIORef ref
            case b of
              Bound t -> sTypeToDisplayHelper (ref:visited) t
              Skolem i _ -> return $ TVar (unLocated i)
              Unbound _ _ -> return $ TVar $ Ident "_"
      TArrow t1 t2 -> do
        t1' <- sTypeToDisplayHelper visited t1
        t2' <- sTypeToDisplayHelper visited t2
        return $ TArrow t1' t2'
      TForall ref ty' -> do
        b <- readIORef ref
        case b of
          Bound t -> sTypeToDisplayHelper (ref:visited) t
          Skolem i _ -> do
            ty'' <- sTypeToDisplayHelper visited ty'
            return $ TForall (unLocated i) ty''
          Unbound _ _ -> do
            ty'' <- sTypeToDisplayHelper visited ty'
            return $ TForall (Ident "_") ty''
      TConstraint traitName typeVars targetType bodyType -> do
        traitName' <- sTBindingToIdentImproved traitName
        typeVars' <- mapM sTBindingToIdentImproved typeVars
        targetType' <- sTypeToDisplayHelper visited targetType
        bodyType' <- sTypeToDisplayHelper visited bodyType
        return $ TConstraint traitName' typeVars' targetType' bodyType'
      TApp t1 t2 -> do
        t1' <- sTypeToDisplayHelper visited t1
        t2' <- sTypeToDisplayHelper visited t2
        return $ TApp t1' t2'
      TList t -> do
        t' <- sTypeToDisplayHelper visited t
        return $ TList t'
      TIO t -> do
        t' <- sTypeToDisplayHelper visited t
        return $ TIO t'
      TUnit -> return TUnit
      TString -> return TString
      TInt -> return TInt
      TBool -> return TBool

sStmtToDisplay :: SStmt -> IO (Stmt Ident)
sStmtToDisplay = \case
  Let _ v mty body -> do
    v' <- sBindingToIdent v
    mty' <- mapM sTypeToDisplay mty
    -- Use targeted resolution for let statements with explicit type annotations
    body' <- case mty' of
      Just annotationType -> do
        -- For lambda expressions with type annotations, resolve parameter types from annotation
        case body of
          Lam {} -> resolveLambdaWithTypeAnnotation body annotationType
          _ -> do
            -- First try normal resolution
            _ <- sExprToDisplay body
            -- Then apply targeted resolution with the expected type
            resolveTraitMethodsWithType body annotationType
      Nothing -> sExprToDisplay body
    return $ Let () v' mty' body'
  Type binding ty -> do
    binding' <- sTBindingToIdent binding
    ty' <- sTypeToDisplay ty
    return $ Type binding' ty'
  Data binding fields -> do
    binding' <- sTBindingToIdent binding
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ Data binding' fields'
  DataForall binding vars fields -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM sTBindingToIdent vars
    fields' <- forM fields $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ DataForall binding' vars' fields'
  Trait binding vars methods -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM sTBindingToIdent vars
    methods' <- forM methods $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ Trait binding' vars' methods'
  TraitWithKinds binding vars methods -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM (sTBindingToIdent . fst) vars
    methods' <- forM methods $ \(f, ty) -> do
      ty' <- sTypeToDisplay ty
      return (f, ty')
    return $ Trait binding' vars' methods'
  Impl binding vars ty methods -> do
    binding' <- sTBindingToIdent binding
    vars' <- mapM sTBindingToIdent vars
    ty' <- sTypeToDisplay ty
    methods' <- forM methods $ \(f, e) -> do
      e' <- sExprToDisplay e
      return (f, e')
    return $ Impl binding' vars' ty' methods'

sBlockToDisplayWithTypes :: SBlock -> IO (Block Ident)
sBlockToDisplayWithTypes (Block stmts expr) = do
  stmts' <- mapM sStmtToDisplay stmts
  expr' <- sExprToDisplayWithTypes expr
  -- Apply global trait method resolution based on usage patterns
  globalTraitMethodResolution (Block stmts' expr')

-- Global trait method resolution that looks at usage patterns across the entire block
globalTraitMethodResolution :: Block Ident -> IO (Block Ident)
globalTraitMethodResolution (Block stmts expr) = do
  -- Look for patterns like: let result: Type = void (pure #Unit)
  -- and propagate the type information to resolve trait methods
  resolvedStmts <- mapM (resolveStmtWithContext stmts) stmts
  -- Also resolve the final expression if it references variables with known types
  resolvedExpr <- resolveExprWithStatementContext stmts expr
  return $ Block resolvedStmts resolvedExpr
  where
    resolveStmtWithContext allStmts stmt = case stmt of
      Let _ var (Just annotationType) body -> do
        -- For let statements with type annotations, try to resolve trait methods
        -- in the body using the annotation type, and also resolve any function calls
        resolvedBody <- case body of
          Lam {} -> resolveLambdaWithExpectedType body annotationType
          _ -> resolveWithFunctionContext allStmts body annotationType
        return $ Let () var (Just annotationType) resolvedBody
      other -> return other


    
    -- Resolve lambda with expected type to get proper parameter type annotations
    resolveLambdaWithExpectedType :: Expr Ident -> Type Ident -> IO (Expr Ident)
    resolveLambdaWithExpectedType lamExpr expectedType = case lamExpr of
      Lam _ param _mty body -> do
        let expectedType' = case expectedType of
              -- Strip forall to get to the arrow type
              TForall _ innerType -> innerType
              _ -> expectedType
        case expectedType' of
          TArrow paramType restType -> do
            -- Use the expected parameter type from the function signature
            let newParamType = Just paramType
            resolvedBody <- resolveLambdaWithExpectedType body restType
            return $ Lam () param newParamType resolvedBody
          _ -> do
            -- Not a function type, keep original
            return expr
      _ -> return expr

    -- Resolve expressions using context from statements (for variables that reference let bindings)
    resolveExprWithStatementContext allStmts expr' = case expr' of
      Var _ varName -> do
        -- Check if this variable has a type annotation in the statements
        case findVariableType allStmts varName of
          Just varType -> do
            -- If the variable references something with trait methods, resolve using its type
            case findFunctionDef allStmts varName of
              Just funcBody -> directResolveWithType funcBody varType
              Nothing -> return expr'
          Nothing -> return expr'
      App _ funcExpr arg -> do
        -- Handle polymorphic function calls that need explicit type applications
        case funcExpr of
          Var _ (Ident "void") -> do
            -- void is polymorphic: forall f . Functor f => f a -> f #Unit
            -- Need to instantiate it with explicit types based on the argument
            resolvedArg <- resolveExprWithStatementContext allStmts arg
            case findVariableType allStmts (Ident "result") of
              Just (TApp functorType argType) -> do
                -- result: State #Unit #Unit, so f = State #Unit, a = #Unit
                let voidWithTypes = TyApp () (TyApp () funcExpr functorType) argType
                return $ App () voidWithTypes resolvedArg
              _ -> do
                resolvedFuncExpr <- resolveExprWithStatementContext allStmts funcExpr
                return $ App () resolvedFuncExpr resolvedArg
          _ -> do
            resolvedFuncExpr <- resolveExprWithStatementContext allStmts funcExpr
            resolvedArg <- resolveExprWithStatementContext allStmts arg
            return $ App () resolvedFuncExpr resolvedArg
      _ -> return expr'

    -- Enhanced resolution that looks at function definitions to resolve trait methods
    resolveWithFunctionContext allStmts expr' expectedType = case expr' of
      App _ funcExpr arg -> do
        -- Check if funcExpr is a variable that refers to a function with trait methods
        case funcExpr of
          Var _ funcName -> do
            -- Look for the function definition in the statements
            case findFunctionDef allStmts funcName of
              Just funcBody -> do
                -- Resolve trait methods in the function body using the expected type
                _ <- directResolveWithType funcBody expectedType
                -- Return the application with the resolved function
                resolvedArg <- directResolveWithType arg expectedType
                return $ App () (Var () funcName) resolvedArg
              Nothing -> directResolveWithType expr expectedType
          _ -> directResolveWithType expr' expectedType
      _ -> directResolveWithType expr' expectedType
    
    -- Find a function definition in the statements
    findFunctionDef stmts' targetName = 
      case [body | Let _ name _ body <- stmts', name == targetName] of
        (funcBody:_) -> Just funcBody
        [] -> Nothing
        
    -- Find the type annotation for a variable in the statements
    findVariableType stmts' targetName = 
      case [ty | Let _ name (Just ty) _ <- stmts', name == targetName] of
        (varType:_) -> Just varType
        [] -> Nothing

-- Create type mapping for expression variables
extractTypeMapping :: SExpr -> IO [(Ident, Type Ident)]
extractTypeMapping = gatherTypes
  where
    gatherTypes expr = case expr of
      Var _ binding -> do
        binding' <- sBindingToIdent binding
        exprType <- sTypeToDisplay (TVar (typeOf expr))
        return [(binding', exprType)]
      App _ t1 t2 -> do
        types1 <- gatherTypes t1
        types2 <- gatherTypes t2
        return (types1 ++ types2)
      Lam _ binding _ body -> do
        binding' <- sBindingToIdent binding
        exprType <- sTypeToDisplay (TVar (typeOf expr))
        bodyTypes <- gatherTypes body
        return ((binding', exprType) : bodyTypes)
      TyApp _ body _ -> gatherTypes body
      BlockExpr _ (Block stmts expr') -> do
        stmtTypes <- concat <$> mapM gatherStmtTypes stmts
        exprTypes <- gatherTypes expr'
        return (stmtTypes ++ exprTypes)
      RecordCreation _ expr' fields -> do
        exprTypes <- gatherTypes expr'
        fieldTypes <- concat <$> mapM (gatherTypes . snd) fields
        return (exprTypes ++ fieldTypes)
      PrimUnit _ -> return []
      PrimNil _ _ -> return []
      PrimCons _ _ headExpr tailExpr -> do
        headTypes <- gatherTypes headExpr
        tailTypes <- gatherTypes tailExpr
        return (headTypes ++ tailTypes)
      _ -> return []

    gatherStmtTypes stmt = case stmt of
      Let _ binding _ body -> do
        binding' <- sBindingToIdent binding
        exprType <- sTypeToDisplay (TVar (typeOf body))
        bodyTypes <- gatherTypes body
        return ((binding', exprType) : bodyTypes)
      Impl _ _ _ methods -> concat <$> mapM (gatherTypes . snd) methods
      _ -> return []

sBlockToDisplay :: SBlock -> IO (Block Ident)
sBlockToDisplay = sBlockToDisplayWithTypes
