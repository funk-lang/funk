{-# LANGUAGE LambdaCase #-}

module Funk.Interpreter where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as Map
import System.Exit (ExitCode(ExitSuccess, ExitFailure), exitWith)
import Funk.Core

data Value
  = VUnit
  | VString String
  | VInt Int
  | VLam Var CoreType (CoreExpr, Env)
  | VTyLam TyVar (CoreExpr, Env)
  | VCon String [Value]
  | VList [Value]
  | VDict String CoreType (Map String Value)
  | VIO (IO Value)

instance Show Value where
  show VUnit = "()"
  show (VString s) = show s
  show (VInt i) = show i
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
  (VString s1) == (VString s2) = s1 == s2
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
  TyString -> TyString
  TyInt -> TyInt
  TyBool -> TyBool
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
    -- For lambda values, create a recursive binding using a fixpoint
    let updatedVal = case valResult of
          VLam lamVar ty (lamBody, closure) -> 
            let recursiveVal = VLam lamVar ty (lamBody, Map.insert var recursiveVal closure)
            in recursiveVal
          _ -> valResult
    withVar var updatedVal (eval body)
  CoreCase scrut alts -> do
    scrutVal <- eval scrut
    evalCase scrutVal alts
  CoreCon name args -> do
    argVals <- mapM eval args
    return $ VCon name argVals
  CoreUnit -> return VUnit
  CoreString s -> return $ VString s
  CoreInt i -> return $ VInt i
  CoreTrue -> return $ VCon "True" []
  CoreFalse -> return $ VCon "False" []
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
  CoreBind expr1 expr2 -> do
    val1 <- eval expr1
    val2 <- eval expr2
    case (val1, val2) of
      (VIO io1, VLam var _ty (body, closure)) -> do
        return $ VIO $ do
          result1 <- io1
          case runInterpreterWithEnv (Map.insert var result1 closure) Map.empty body of
            Left err -> error $ "bind error: " ++ err
            Right (VIO nextAction) -> nextAction
            Right val -> return val
      _ -> throwError "Type error: bind expects IO action and function"
  CorePrint expr -> do
    val <- eval expr
    return $ VIO $ do
      putStrLn $ prettyValue val
      return VUnit
  CoreFmapIO f io -> do
    fVal <- eval f
    ioVal <- eval io
    case (fVal, ioVal) of
      (VLam var _ty (body, closure), VIO ioAction) -> do
        return $ VIO $ do
          result <- ioAction
          case runInterpreterWithEnv (Map.insert var result closure) Map.empty body of
            Left err -> error $ "fmapIO error: " ++ err
            Right val -> return val
      _ -> throwError "Type error: fmapIO expects function and IO action"
  CorePureIO expr -> do
    val <- eval expr
    return $ VIO (return val)
  CoreApplyIO iof iox -> do
    iofVal <- eval iof
    ioxVal <- eval iox
    case (iofVal, ioxVal) of
      (VIO fAction, VIO xAction) -> do
        return $ VIO $ do
          f <- fAction
          x <- xAction
          case f of
            VLam var _ty (body, closure) -> do
              case runInterpreterWithEnv (Map.insert var x closure) Map.empty body of
                Left err -> error $ "applyIO error: " ++ err
                Right val -> return val
            _ -> error "Type error: applyIO expects function in IO"
      _ -> throwError "Type error: applyIO expects two IO actions"
  CoreBindIO iox f -> do
    ioxVal <- eval iox
    fVal <- eval f
    case (ioxVal, fVal) of
      (VIO xAction, VLam var _ty (body, closure)) -> do
        return $ VIO $ do
          x <- xAction
          case runInterpreterWithEnv (Map.insert var x closure) Map.empty body of
            Left err -> error $ "bindIO error: " ++ err
            Right (VIO nextAction) -> nextAction
            Right val -> return val
      _ -> throwError "Type error: bindIO expects IO action and function"

  CoreIntEq e1 e2 -> do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
      (VInt i1, VInt i2) -> return $ if i1 == i2 then VCon "True" [] else VCon "False" []
      _ -> throwError "Type error: intEq expects two integers"

  CoreStringEq e1 e2 -> do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
      (VString s1, VString s2) -> return $ if s1 == s2 then VCon "True" [] else VCon "False" []
      _ -> throwError "Type error: stringEq expects two strings"

  CoreIfThenElse c t e -> do
    v <- eval c
    case v of
      VCon "True" [] -> do
        vt <- eval t
        applyFunction vt (VCon "Unit" [])
      VCon "False" [] -> do
        ve <- eval e
        applyFunction ve (VCon "Unit" [])
      _ -> throwError "Type error: if condition must be a boolean"

  CoreIntSub e1 e2 -> do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
      (VInt i1, VInt i2) -> return $ VInt (i1 - i2)
      _ -> throwError "Type error: intSub expects two integers"

  CoreExit e -> do
    v <- eval e
    case v of
      VInt code -> return $ VIO $ do
        exitWith (if code == 0 then ExitSuccess else ExitFailure code)
      _ -> throwError "Type error: exit expects an integer"

  CoreStringConcat e1 e2 -> do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
      (VString s1, VString s2) -> return $ VString (s1 ++ s2)
      _ -> throwError "Type error: stringConcat expects two strings"

  -- Primitive values (for currying) - simple lambda approach
  CoreFmapIOValue -> return $ VLam (Var "f") TyUnit (CoreLam (Var "io") TyUnit (CoreFmapIO (CoreVar (Var "f")) (CoreVar (Var "io"))), Map.empty)
  CorePureIOValue -> return $ VLam (Var "x") TyUnit (CorePureIO (CoreVar (Var "x")), Map.empty)
  CoreApplyIOValue -> return $ VLam (Var "iof") TyUnit (CoreLam (Var "iox") TyUnit (CoreApplyIO (CoreVar (Var "iof")) (CoreVar (Var "iox"))), Map.empty)
  CoreBindIOValue -> return $ VLam (Var "iox") TyUnit (CoreLam (Var "f") TyUnit (CoreBindIO (CoreVar (Var "iox")) (CoreVar (Var "f"))), Map.empty)
  CoreIntEqValue -> return $ VLam (Var "x") TyUnit (CoreLam (Var "y") TyUnit (CoreIntEq (CoreVar (Var "x")) (CoreVar (Var "y"))), Map.empty)
  CoreStringEqValue -> return $ VLam (Var "x") TyUnit (CoreLam (Var "y") TyUnit (CoreStringEq (CoreVar (Var "x")) (CoreVar (Var "y"))), Map.empty)
  CoreStringConcatValue -> return $ VLam (Var "x") TyUnit (CoreLam (Var "y") TyUnit (CoreStringConcat (CoreVar (Var "x")) (CoreVar (Var "y"))), Map.empty)
  CoreIfThenElseValue -> return $ VLam (Var "c") TyUnit (CoreLam (Var "t") TyUnit (CoreLam (Var "e") TyUnit (CoreIfThenElse (CoreVar (Var "c")) (CoreVar (Var "t")) (CoreVar (Var "e")))), Map.empty)
  CoreIntSubValue -> return $ VLam (Var "x") TyUnit (CoreLam (Var "y") TyUnit (CoreIntSub (CoreVar (Var "x")) (CoreVar (Var "y"))), Map.empty)
  CoreExitValue -> return $ VLam (Var "code") TyUnit (CoreExit (CoreVar (Var "code")), Map.empty)
  CorePrintValue -> return $ VLam (Var "str") TyUnit (CorePrint (CoreVar (Var "str")), Map.empty)

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
evalProgramIO (CoreProgram _dataTypes main) = do
  result <- runInterpreterIO main
  case result of
    Right (VCon "Record1" [VIO ioAction]) -> do
      -- This is our IO wrapper - execute the IO action and return VUnit
      _ <- ioAction
      return $ Right VUnit
    _ -> return result

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
  VString s -> s
  VInt i -> show i
  VLam var ty _ -> "λ" ++ show var ++ ":" ++ show ty ++ ". <closure>"
  VTyLam tyvar _ -> "Λ" ++ show tyvar ++ ". <closure>"
  VCon name [] -> name
  VCon name args -> name ++ "(" ++ unwords (map prettyValue args) ++ ")"
  VList [] -> "[]"
  VList vs -> "[" ++ unwords (map prettyValue vs) ++ "]"
  VDict traitName targetType _ -> "<" ++ traitName ++ "@" ++ show targetType ++ " dictionary>"
  VIO _ -> "<IO action>"