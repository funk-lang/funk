{-# LANGUAGE LambdaCase #-}

module Funk.Interpreter where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Core

-- | Values in the interpreter
data Value
  = VUnit                           -- Unit value
  | VLam Var CoreType (CoreExpr, Env) -- Lambda closure (var, type, body, environment)
  | VTyLam TyVar (CoreExpr, Env)    -- Type lambda closure (tyvar, body, environment)
  | VCon String [Value]             -- Constructor applied to values
  | VList [Value]                   -- List of values
  | VDict String CoreType (Map String Value) -- Dictionary with methods
  deriving (Show, Eq)

-- | Environment for variable bindings
type Env = Map Var Value

-- | Type environment for type variable bindings
type TyEnv = Map TyVar CoreType

-- | Interpreter monad combining Reader for environments and Except for errors
type Interp = ReaderT (Env, TyEnv) (Except String)

-- | Runtime errors
data InterpError = 
    UnboundVariable Var
  | UnboundTypeVariable TyVar
  | TypeMismatch String
  | PatternMatchFailure
  | UnsupportedOperation String
  deriving (Show, Eq)

-- | Run the interpreter with an empty environment
runInterpreter :: CoreExpr -> Either String Value
runInterpreter expr = runExcept $ runReaderT (eval expr) (Map.empty, Map.empty)

-- | Run the interpreter with an initial environment
runInterpreterWithEnv :: Env -> TyEnv -> CoreExpr -> Either String Value
runInterpreterWithEnv env tyEnv expr = runExcept $ runReaderT (eval expr) (env, tyEnv)

-- | Lookup a variable in the environment
lookupVar :: Var -> Interp Value
lookupVar var = do
  (env, _) <- ask
  case Map.lookup var env of
    Just val -> return val
    Nothing -> throwError $ "Unbound variable: " ++ show var

-- | Lookup a type variable in the type environment
lookupTyVar :: TyVar -> Interp CoreType
lookupTyVar tyvar = do
  (_, tyEnv) <- ask
  case Map.lookup tyvar tyEnv of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound type variable: " ++ show tyvar

-- | Extend the environment with a new binding
withVar :: Var -> Value -> Interp a -> Interp a
withVar var val = local (\(env, tyEnv) -> (Map.insert var val env, tyEnv))

-- | Extend the type environment with a new binding
withTyVar :: TyVar -> CoreType -> Interp a -> Interp a
withTyVar tyvar ty = local (\(env, tyEnv) -> (env, Map.insert tyvar ty tyEnv))

-- | Type substitution in core types
substType :: TyVar -> CoreType -> CoreType -> CoreType
substType tyvar replacement ty = case ty of
  CoreTyVar tv -> if tv == tyvar then replacement else ty
  TyArrow t1 t2 -> TyArrow (substType tyvar replacement t1) (substType tyvar replacement t2)
  TyForall tv t -> if tv == tyvar then ty else TyForall tv (substType tyvar replacement t)
  TyApp t1 t2 -> TyApp (substType tyvar replacement t1) (substType tyvar replacement t2)
  TyUnit -> TyUnit
  TyList t -> TyList (substType tyvar replacement t)
  TyCon name -> TyCon name

-- | Main evaluation function
eval :: CoreExpr -> Interp Value
eval = \case
  CoreVar var -> lookupVar var
  
  CoreLam var ty body -> do
    (env, _) <- ask
    return $ VLam var ty (body, env)
  
  CoreApp func arg -> do
    funcVal <- eval func
    argVal <- eval arg
    applyFunction funcVal argVal
  
  CoreTyLam tyvar body -> do
    (env, _) <- ask
    return $ VTyLam tyvar (body, env)
  
  CoreTyApp expr ty -> do
    exprVal <- eval expr
    applyType exprVal ty
  
  CoreLet var val body -> do
    valResult <- eval val
    withVar var valResult (eval body)
  
  CoreCase scrut alts -> do
    scrutVal <- eval scrut
    evalCase scrutVal alts
  
  CoreCon name args -> do
    argVals <- mapM eval args
    return $ VCon name argVals
  
  CoreUnit -> return VUnit
  
  CoreNil _ty -> return $ VList []
  
  CoreCons _ty headExpr tailExpr -> do
    headVal <- eval headExpr
    tailVal <- eval tailExpr
    case tailVal of
      VList vs -> return $ VList (headVal : vs)
      _ -> throwError "Type error: cons tail must be a list"
  
  CoreDict traitName targetType methods -> do
    methodVals <- mapM eval methods
    let methodNames = ["fmap", "pure", "bind"] -- This should be extracted from trait definitions
    let methodMap = Map.fromList (zip methodNames methodVals)
    return $ VDict traitName targetType methodMap
  
  CoreDictAccess dict methodName -> do
    dictVal <- eval dict
    case dictVal of
      VDict traitName targetType methods -> 
        case Map.lookup methodName methods of
          Just method -> return method
          Nothing -> do
            -- Try to provide built-in implementations for basic traits
            builtInMethod <- getBuiltInMethod traitName targetType methodName
            case builtInMethod of
              Just method -> return method
              Nothing -> throwError $ "Method not found: " ++ methodName ++ " in trait " ++ traitName
      _ -> throwError "Type error: dictionary access on non-dictionary"

-- | Apply a function value to an argument value
applyFunction :: Value -> Value -> Interp Value
applyFunction funcVal argVal = case funcVal of
  VLam var _ty (body, closure) -> do
    (_, tyEnv) <- ask
    local (const (Map.insert var argVal closure, tyEnv)) (eval body)
  _ -> throwError $ "Type error: attempting to apply non-function: " ++ show funcVal

-- | Apply a type abstraction to a type
applyType :: Value -> CoreType -> Interp Value
applyType val ty = case val of
  VTyLam tyvar (body, closure) -> do
    (_, tyEnv) <- ask
    -- Substitute the type in the body and evaluate
    local (const (closure, Map.insert tyvar ty tyEnv)) (eval body)
  _ -> throwError $ "Type error: attempting to apply type to non-type-lambda: " ++ show val

-- | Evaluate a case expression
evalCase :: Value -> [(CorePat, CoreExpr)] -> Interp Value
evalCase _scrutVal [] = throwError "Pattern match failure: no matching patterns"
evalCase scrutVal ((pat, expr) : alts) = do
  maybeBindings <- matchPattern pat scrutVal
  case maybeBindings of
    Just bindings -> do
      -- Extend environment with pattern bindings and evaluate expression
      foldM (\acc (var, val) -> local (\(env, tyEnv) -> (Map.insert var val env, tyEnv)) (return ())) () bindings
      (env, tyEnv) <- ask
      let newEnv = foldl (\e (var, val) -> Map.insert var val e) env bindings
      local (const (newEnv, tyEnv)) (eval expr)
    Nothing -> evalCase scrutVal alts

-- | Pattern matching - returns Just bindings if match succeeds, Nothing otherwise
matchPattern :: CorePat -> Value -> Interp (Maybe [(Var, Value)])
matchPattern pat val = case (pat, val) of
  (PatVar var, _) -> return $ Just [(var, val)]
  
  (PatUnit, VUnit) -> return $ Just []
  
  (PatCon patName patVars, VCon conName conArgs) -> 
    if patName == conName && length patVars == length conArgs
      then return $ Just (zip patVars conArgs)
      else return Nothing
  
  _ -> return Nothing

-- | Evaluate a core program
evalProgram :: CoreProgram -> Either String Value
evalProgram (CoreProgram _dataTypes main) = runInterpreter main

-- | Get built-in method implementations for basic traits
getBuiltInMethod :: String -> CoreType -> String -> Interp (Maybe Value)
getBuiltInMethod traitName targetType methodName = case (traitName, methodName, targetType) of
  -- Functor instance for State and Unknown (compiler sometimes generates Unknown)
  ("Functor", "fmap", TyCon "State") -> getFunctorFmap
  ("Functor", "fmap", TyCon "Unknown") -> getFunctorFmap
  
  -- Monad instance for State and Unknown
  ("Monad", "pure", TyCon "State") -> getMonadPure
  ("Monad", "pure", TyCon "Unknown") -> getMonadPure
  ("Monad", "bind", TyCon "State") -> getMonadBind  
  ("Monad", "bind", TyCon "Unknown") -> getMonadBind
  
  _ -> return Nothing
  where
    getFunctorFmap = do
      -- fmap f state = state (for our simple State implementation)
      (env, _) <- ask
      let fmapImpl = VLam (Var "f") TyUnit 
            (CoreLam (Var "state") TyUnit (CoreVar (Var "state")), env)
      return $ Just fmapImpl
      
    getMonadPure = do
      -- pure a = State (\s -> a)
      (env, _) <- ask
      let pureImpl = VLam (Var "a") TyUnit
            (CoreCon "State" [CoreLam (Var "s") TyUnit (CoreVar (Var "a"))], env)
      return $ Just pureImpl
      
    getMonadBind = do
      -- bind state f = state (simplified)
      (env, _) <- ask
      let bindImpl = VLam (Var "state") TyUnit
            (CoreLam (Var "f") TyUnit (CoreVar (Var "state")), env)
      return $ Just bindImpl

-- | Pretty print values
prettyValue :: Value -> String
prettyValue = \case
  VUnit -> "()"
  VLam var ty _ -> "λ" ++ show var ++ ":" ++ show ty ++ ". <closure>"
  VTyLam tyvar _ -> "Λ" ++ show tyvar ++ ". <closure>"
  VCon name [] -> name
  VCon name args -> name ++ "(" ++ unwords (map prettyValue args) ++ ")"
  VList [] -> "[]"
  VList vs -> "[" ++ unwords (map prettyValue vs) ++ "]"
  VDict traitName targetType _ -> "<" ++ traitName ++ "@" ++ show targetType ++ " dictionary>"