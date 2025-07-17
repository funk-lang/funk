{-# LANGUAGE LambdaCase #-}

module Funk.Interpreter where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as Map
import Funk.Core

data Value
  = VUnit
  | VLam Var CoreType (CoreExpr, Env)
  | VTyLam TyVar (CoreExpr, Env)
  | VCon String [Value]
  | VList [Value]
  | VDict String CoreType (Map String Value)
  | VIO (IO Value)

instance Show Value where
  show VUnit = "()"
  show (VLam var ty _) = "λ" ++ show var ++ ":" ++ show ty ++ ". <closure>"
  show (VTyLam tyvar _) = "Λ" ++ show tyvar ++ ". <closure>"
  show (VCon name []) = name
  show (VCon name args) = name ++ "(" ++ unwords (map show args) ++ ")"
  show (VList []) = "[]"
  show (VList vs) = "[" ++ unwords (map show vs) ++ "]"
  show (VDict traitName targetType _) = "<" ++ traitName ++ "@" ++ show targetType ++ " dictionary>"
  show (VIO _) = "<IO action>"

instance Eq Value where
  VUnit == VUnit = True
  (VLam var1 ty1 _) == (VLam var2 ty2 _) = var1 == var2 && ty1 == ty2
  (VTyLam tyvar1 _) == (VTyLam tyvar2 _) = tyvar1 == tyvar2
  (VCon name1 args1) == (VCon name2 args2) = name1 == name2 && args1 == args2
  (VList vs1) == (VList vs2) = vs1 == vs2
  (VDict traitName1 targetType1 _) == (VDict traitName2 targetType2 _) = 
    traitName1 == traitName2 && targetType1 == targetType2
  (VIO _) == (VIO _) = True
  _ == _ = False

type Env = Map Var Value
type TyEnv = Map TyVar CoreType
type Interp = ReaderT (Env, TyEnv) (Except String)

data InterpError = 
    UnboundVariable Var
  | UnboundTypeVariable TyVar
  | TypeMismatch String
  | PatternMatchFailure
  | UnsupportedOperation String
  deriving (Show, Eq)

runInterpreter :: CoreExpr -> Either String Value
runInterpreter expr = runExcept $ runReaderT (eval expr) (Map.empty, Map.empty)

runInterpreterIO :: CoreExpr -> IO (Either String Value)
runInterpreterIO expr = do
  case runInterpreter expr of
    Left err -> return $ Left err
    Right (VIO ioAction) -> do
      result <- ioAction
      return $ Right result
    Right val -> return $ Right val

runInterpreterWithEnv :: Env -> TyEnv -> CoreExpr -> Either String Value
runInterpreterWithEnv env tyEnv expr = runExcept $ runReaderT (eval expr) (env, tyEnv)

lookupVar :: Var -> Interp Value
lookupVar var = do
  (env, _) <- ask
  case Map.lookup var env of
    Just val -> return val
    Nothing -> throwError $ "Unbound variable: " ++ show var

lookupTyVar :: TyVar -> Interp CoreType
lookupTyVar tyvar = do
  (_, tyEnv) <- ask
  case Map.lookup tyvar tyEnv of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound type variable: " ++ show tyvar

withVar :: Var -> Value -> Interp a -> Interp a
withVar var val = local (\(env, tyEnv) -> (Map.insert var val env, tyEnv))

withTyVar :: TyVar -> CoreType -> Interp a -> Interp a
withTyVar tyvar ty = local (\(env, tyEnv) -> (env, Map.insert tyvar ty tyEnv))

substType :: TyVar -> CoreType -> CoreType -> CoreType
substType tyvar replacement ty = case ty of
  CoreTyVar tv -> if tv == tyvar then replacement else ty
  TyArrow t1 t2 -> TyArrow (substType tyvar replacement t1) (substType tyvar replacement t2)
  TyForall tv t -> if tv == tyvar then ty else TyForall tv (substType tyvar replacement t)
  TyApp t1 t2 -> TyApp (substType tyvar replacement t1) (substType tyvar replacement t2)
  TyUnit -> TyUnit
  TyList t -> TyList (substType tyvar replacement t)
  TyIO t -> TyIO (substType tyvar replacement t)
  TyCon name -> TyCon name

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
    let methodNames = ["fmap", "pure", "bind"]
    let methodMap = Map.fromList (zip methodNames methodVals)
    return $ VDict traitName targetType methodMap
  CoreDictAccess dict methodName -> do
    dictVal <- eval dict
    case dictVal of
      VDict traitName targetType methods -> 
        case Map.lookup methodName methods of
          Just method -> return method
          Nothing -> do
            builtInMethod <- getBuiltInMethod traitName targetType methodName
            case builtInMethod of
              Just method -> return method
              Nothing -> throwError $ "Method not found: " ++ methodName ++ " in trait " ++ traitName
      _ -> throwError "Type error: dictionary access on non-dictionary"
  CoreReturn expr -> do
    val <- eval expr
    return $ VIO (return val)
  CoreBind expr1 _expr2 -> do
    val1 <- eval expr1
    case val1 of
      VIO io1 -> do
        return $ VIO $ do
          result1 <- io1
          case result1 of
            VIO innerIO -> innerIO
            _ -> error "Type error: bind expects IO action"
      _ -> throwError "Type error: bind expects IO action"
  CorePrint expr -> do
    val <- eval expr
    return $ VIO $ do
      putStrLn $ prettyValue val
      return VUnit

applyFunction :: Value -> Value -> Interp Value
applyFunction funcVal argVal = case funcVal of
  VLam var _ty (body, closure) -> do
    (_, tyEnv) <- ask
    local (const (Map.insert var argVal closure, tyEnv)) (eval body)
  _ -> throwError $ "Type error: attempting to apply non-function: " ++ show funcVal

applyType :: Value -> CoreType -> Interp Value
applyType val ty = case val of
  VTyLam tyvar (body, closure) -> do
    (_, tyEnv) <- ask
    local (const (closure, Map.insert tyvar ty tyEnv)) (eval body)
  _ -> throwError $ "Type error: attempting to apply type to non-type-lambda: " ++ show val

evalCase :: Value -> [(CorePat, CoreExpr)] -> Interp Value
evalCase _scrutVal [] = throwError "Pattern match failure: no matching patterns"
evalCase scrutVal ((pat, expr) : alts) = do
  maybeBindings <- matchPattern pat scrutVal
  case maybeBindings of
    Just bindings -> do
      foldM (\_acc (var, val) -> local (\(env, tyEnv) -> (Map.insert var val env, tyEnv)) (return ())) () bindings
      (env, tyEnv) <- ask
      let newEnv = foldl (\e (var, val) -> Map.insert var val e) env bindings
      local (const (newEnv, tyEnv)) (eval expr)
    Nothing -> evalCase scrutVal alts

matchPattern :: CorePat -> Value -> Interp (Maybe [(Var, Value)])
matchPattern pat val = case (pat, val) of
  (PatVar var, _) -> return $ Just [(var, val)]
  (PatUnit, VUnit) -> return $ Just []
  (PatCon patName patVars, VCon conName conArgs) -> 
    if patName == conName && length patVars == length conArgs
      then return $ Just (zip patVars conArgs)
      else return Nothing
  _ -> return Nothing

evalProgram :: CoreProgram -> Either String Value
evalProgram (CoreProgram _dataTypes main) = runInterpreter main

evalProgramIO :: CoreProgram -> IO (Either String Value)
evalProgramIO (CoreProgram _dataTypes main) = runInterpreterIO main

getBuiltInMethod :: String -> CoreType -> String -> Interp (Maybe Value)
getBuiltInMethod traitName targetType methodName = case (traitName, methodName, targetType) of
  ("Functor", "fmap", TyCon "State") -> getFunctorFmap
  ("Functor", "fmap", TyCon "Unknown") -> getFunctorFmap
  ("Monad", "pure", TyCon "State") -> getMonadPure
  ("Monad", "pure", TyCon "Unknown") -> getMonadPure
  ("Monad", "bind", TyCon "State") -> getMonadBind  
  ("Monad", "bind", TyCon "Unknown") -> getMonadBind
  _ -> return Nothing
  where
    getFunctorFmap = do
      (env, _) <- ask
      let fmapImpl = VLam (Var "f") TyUnit 
            (CoreLam (Var "state") TyUnit (CoreVar (Var "state")), env)
      return $ Just fmapImpl
    getMonadPure = do
      (env, _) <- ask
      let pureImpl = VLam (Var "a") TyUnit
            (CoreCon "State" [CoreLam (Var "s") TyUnit (CoreVar (Var "a"))], env)
      return $ Just pureImpl
    getMonadBind = do
      (env, _) <- ask
      let bindImpl = VLam (Var "state") TyUnit
            (CoreLam (Var "f") TyUnit (CoreVar (Var "state")), env)
      return $ Just bindImpl

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
  VIO _ -> "<IO action>"