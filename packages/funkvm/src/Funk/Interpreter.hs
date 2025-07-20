{-|
Module      : Funk.Interpreter
Description : Interpreter for Funk Core IR
Copyright   : (c) 2025  
License     : MIT

This module provides the runtime interpreter for Funk Core IR.
It evaluates Core expressions in an environment and handles
primitive operations, function application, and IO actions.
-}
module Funk.Interpreter where

import Funk.Core
import Funk.Core.Parser
import Control.Monad (foldM)
import qualified Data.Map as Map
import System.Exit (exitWith, ExitCode(..))

-- | Runtime values
data Value
  = VUnit
  | VInt Int
  | VString String
  | VBool Bool
  | VClosure String CoreType CoreExpr Env  -- variable name, type, body, closure env
  | VList [Value]
  | VCon String [Value]
  | VPrimitive CorePrimitive [Value]  -- Partially applied primitive
  deriving (Show, Eq)

-- | Environment mapping variable names to values
type Env = Map.Map String Value

-- | Evaluation monad
type Eval = IO

-- | Evaluate a core expression in an environment
eval :: Env -> CoreExpr -> Eval Value
eval env expr = case expr of
  CoreVar (Var name) -> 
    case Map.lookup name env of
      Just val -> return val
      Nothing -> error $ "Unbound variable: " ++ name

  CoreLam (Var var) ty body -> 
    return $ VClosure var ty body env

  CoreApp e1 e2 -> do
    v1 <- eval env e1
    v2 <- eval env e2
    apply v1 v2

  CoreTyLam _ body -> 
    -- Type lambdas are erased at runtime
    eval env body

  CoreTyApp e _ -> 
    -- Type applications are erased at runtime
    eval env e

  CoreLet (Var var) val body -> do
    v <- eval env val
    let env' = Map.insert var v env
    eval env' body

  CoreCase scrut alts -> do
    scrutVal <- eval env scrut
    evalCase env scrutVal alts

  CoreCon name args -> do
    argVals <- mapM (eval env) args
    return $ VCon name argVals

  CoreUnit -> return VUnit
  CoreString s -> return $ VString s
  CoreInt i -> return $ VInt i
  CoreTrue -> return $ VBool True
  CoreFalse -> return $ VBool False

  CoreNil _ -> return $ VList []

  CoreCons _ headExpr tailExpr -> do
    headVal <- eval env headExpr
    tailVal <- eval env tailExpr
    case tailVal of
      VList xs -> return $ VList (headVal : xs)
      _ -> error "cons: tail is not a list"

  CoreDict _ _ methods -> do
    -- For now, just evaluate the first method as a simple dictionary
    case methods of
      [method] -> eval env method
      _ -> error "Dictionary evaluation not fully implemented"

  CoreDictAccess dict _ -> 
    -- For now, just return the dictionary itself
    eval env dict

  CoreReturn e -> do
    -- IO return - just evaluate the expression for now
    eval env e

  CoreBind e1 e2 -> do
    -- IO bind - evaluate e1, then apply e2 to unit
    _ <- eval env e1
    apply2 env e2 VUnit

  CorePrim prim args -> do
    argVals <- mapM (eval env) args
    case prim of
      -- Fully saturated primitives
      PrimPrint -> case argVals of
        [VString s] -> do
          putStrLn s
          return VUnit
        [val] -> do
          putStrLn (showValue val)
          return VUnit
        [] -> return $ VPrimitive prim []
        _ -> error "print: too many arguments"

      PrimIntEq -> case argVals of
        [VInt a, VInt b] -> return $ VBool (a == b)
        [VInt a] -> return $ VPrimitive prim [VInt a]
        [] -> return $ VPrimitive prim []
        _ -> error "intEq: wrong argument types"

      PrimIntSub -> case argVals of
        [VInt a, VInt b] -> return $ VInt (a - b)
        [VInt a] -> return $ VPrimitive prim [VInt a]
        [] -> return $ VPrimitive prim []
        _ -> error "intSub: wrong argument types"

      PrimStringEq -> case argVals of
        [VString a, VString b] -> return $ VBool (a == b)
        [VString a] -> return $ VPrimitive prim [VString a]
        [] -> return $ VPrimitive prim []
        _ -> error "stringEq: wrong argument types"

      PrimStringConcat -> case argVals of
        [VString a, VString b] -> return $ VString (a ++ b)
        [VString a] -> return $ VPrimitive prim [VString a]
        [] -> return $ VPrimitive prim []
        _ -> error "stringConcat: wrong argument types"

      PrimIfThenElse -> case argVals of
        [VBool cond, thenFn, elseFn] -> do
          if cond 
            then apply thenFn VUnit
            else apply elseFn VUnit
        [VBool cond, thenFn] -> return $ VPrimitive prim [VBool cond, thenFn]
        [VBool cond] -> return $ VPrimitive prim [VBool cond]
        [] -> return $ VPrimitive prim []
        _ -> error "ifThenElse: wrong argument types"

      PrimExit -> case argVals of
        [VInt code] -> do
          exitWith (if code == 0 then ExitSuccess else ExitFailure code)
        [] -> return $ VPrimitive prim []
        _ -> error "exit: wrong argument types"

      _ -> return $ VPrimitive prim argVals

-- | Apply a function value to an argument
apply :: Value -> Value -> Eval Value
apply (VClosure var _ body env) arg = do
  let env' = Map.insert var arg env
  eval env' body
apply (VPrimitive prim args) arg = do
  eval Map.empty (CorePrim prim (map valueToExpr (args ++ [arg])))
apply f _ = error $ "Cannot apply non-function: " ++ show f

-- | Apply a function to an argument in an environment
apply2 :: Env -> CoreExpr -> Value -> Eval Value
apply2 env funcExpr arg = do
  func <- eval env funcExpr
  apply func arg

-- | Evaluate case alternatives
evalCase :: Env -> Value -> [(CorePat, CoreExpr)] -> Eval Value
evalCase _ scrutVal [] = error $ "No matching pattern for: " ++ show scrutVal
evalCase env scrutVal ((pat, expr):alts) = do
  maybeEnv <- matchPattern env pat scrutVal
  case maybeEnv of
    Just env' -> eval env' expr
    Nothing -> evalCase env scrutVal alts

-- | Pattern matching
matchPattern :: Env -> CorePat -> Value -> Eval (Maybe Env)
matchPattern env (PatVar (Var var)) val = 
  return $ Just $ Map.insert var val env
matchPattern env PatUnit VUnit = 
  return $ Just env
matchPattern env (PatCon name vars) (VCon name' vals) 
  | name == name' && length vars == length vals = do
      let bindings = zip (map (\(Var v) -> v) vars) vals
      return $ Just $ foldr (uncurry Map.insert) env bindings
matchPattern _ _ _ = return Nothing

-- | Convert a value back to an expression (for primitives)
valueToExpr :: Value -> CoreExpr
valueToExpr VUnit = CoreUnit
valueToExpr (VInt i) = CoreInt i
valueToExpr (VString s) = CoreString s
valueToExpr (VBool True) = CoreTrue
valueToExpr (VBool False) = CoreFalse
valueToExpr v = error $ "Cannot convert value to expression: " ++ show v

-- | Show a value in a user-friendly way
showValue :: Value -> String
showValue VUnit = "()"
showValue (VInt i) = show i
showValue (VString s) = s
showValue (VBool True) = "True"
showValue (VBool False) = "False"
showValue (VList vals) = "[" ++ unwords (map showValue vals) ++ "]"
showValue (VCon name []) = name
showValue (VCon name vals) = name ++ " " ++ unwords (map showValue vals)
showValue (VClosure _ _ _ _) = "<function>"
showValue (VPrimitive prim _) = "<primitive " ++ show prim ++ ">"

-- | Load a Core module from bindings
loadModule :: CoreModule -> Env -> Eval Env
loadModule (CoreLibrary _ bindings) env = do
  foldM loadBinding env bindings
loadModule (CoreProgram' _) env = do
  -- For programs, we don't load bindings into the environment
  -- The main expression will be evaluated separately
  return env

-- | Load a single binding into the environment
loadBinding :: Env -> CoreBinding -> Eval Env
loadBinding env (CoreBinding name _ expr) = do
  val <- eval env expr
  return $ Map.insert name val env

-- | Interpret a core module
interpretCore :: CoreModule -> IO ()
interpretCore coreModule = do
  env <- loadModule coreModule Map.empty
  case coreModule of
    CoreLibrary _ _ -> 
      putStrLn "Library loaded successfully."
    CoreProgram' (CoreProgram _ mainExpr) -> do
      _ <- eval env mainExpr
      return ()

-- | Load and interpret multiple .funkc files
loadModules :: [FilePath] -> IO (Either String Env)
loadModules filePaths = do
  result <- foldM loadFile (Right Map.empty) filePaths
  return result
  where
    loadFile (Left err) _ = return $ Left err
    loadFile (Right env) filePath = do
      content <- readFile filePath
      case parseFunkcFile content of
        Left parseErr -> return $ Left $ "Parse error in " ++ filePath ++ ": " ++ show parseErr
        Right coreModule -> do
          env' <- loadModule coreModule env
          return $ Right env'

-- | Execute a main value (should be an IO action)
executeMain :: Value -> IO ()
executeMain mainValue = case mainValue of
  VPrimitive PrimPrint [VString s] -> putStrLn s
  VPrimitive PrimPrint [] -> return ()  -- Print nothing for empty print
  _ -> return ()  -- For other values, execute silently

-- | Run a funkc program with its dependencies
runProgram :: FilePath -> [FilePath] -> IO ()
runProgram mainFile libFiles = do
  -- Load library modules first
  libResult <- loadModules libFiles
  case libResult of
    Left err -> putStrLn $ "Error loading libraries: " ++ err
    Right libEnv -> do
      -- Load main module
      mainContent <- readFile mainFile
      case parseFunkcFile mainContent of
        Left parseErr -> putStrLn $ "Parse error in main file: " ++ show parseErr
        Right mainModule -> do
          env <- loadModule mainModule libEnv
          -- Look for main binding in the environment
          case Map.lookup "main" env of
            Just mainValue -> executeMain mainValue
            Nothing -> putStrLn "No main function found in the program."
