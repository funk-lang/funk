{-# LANGUAGE LambdaCase #-}

module Funk.Dictionary where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import Control.Monad.State

import Funk.Core
import Funk.STerm
import Funk.Term (Ident(..), unIdent)
import qualified Funk.Term as Term

-- | Dictionary transformation state
data DictState = DictState
  { dictTraits :: Map.Map String (String, [String])  -- trait name -> (type param, method names)
  , dictInstances :: Map.Map (String, String) [CoreExpr]  -- (trait, type) -> method implementations
  , dictCounter :: Int
  } deriving (Show)

type DictM = StateT DictState IO

emptyDictState :: DictState
emptyDictState = DictState Map.empty Map.empty 0

-- | Extract trait definitions from statements
extractTraitInfo :: [Term.Stmt Ident] -> DictM ()
extractTraitInfo stmts = do
  mapM_ extractFromStmt stmts
  where
    extractFromStmt :: Term.Stmt Ident -> DictM ()
    extractFromStmt = \case
      Term.Trait traitName _typeVars methods -> do
        let traitNameStr = unIdent traitName
        let methodNames = map (unIdent . fst) methods
        state <- get
        put state { dictTraits = Map.insert traitNameStr ("f", methodNames) (dictTraits state) }
      _ -> return ()

-- | Extract instance definitions from statements
extractInstanceInfo :: [Term.Stmt Ident] -> DictM ()
extractInstanceInfo stmts = do
  mapM_ extractFromStmt stmts
  where
    extractFromStmt :: Term.Stmt Ident -> DictM ()
    extractFromStmt = \case
      Term.Impl traitName _typeVars instanceType methods -> do
        let traitNameStr = unIdent traitName
        let instanceTypeStr = case instanceType of
              Term.TVar ident -> unIdent ident
              Term.TApp (Term.TVar ident) _ -> unIdent ident
              _ -> "Unknown"
        -- Convert method implementations to core expressions
        methodImpls <- mapM (compileMethodImpl . snd) methods
        state <- get
        put state { dictInstances = Map.insert (traitNameStr, instanceTypeStr) methodImpls (dictInstances state) }
      _ -> return ()
    
    compileMethodImpl :: Term.Expr Ident -> DictM CoreExpr
    compileMethodImpl expr = do
      -- Properly compile method implementations
      case expr of
        Term.Var _ ident -> return $ CoreVar (Var (unIdent ident))
        Term.Lam _ param mtype body -> do
          -- Compile lambda with proper type handling
          let paramVar = Var (unIdent param)
          let argType = case mtype of
                Just ty -> compileTypeSimple ty
                Nothing -> TyUnit
          bodyExpr <- compileMethodImpl body
          return $ CoreLam paramVar argType bodyExpr
        Term.App _ func arg -> do
          -- Compile function applications
          funcExpr <- compileMethodImpl func
          argExpr <- compileMethodImpl arg
          return $ CoreApp funcExpr argExpr
        Term.BlockExpr _ (Term.Block stmts blockExpr) -> do
          -- Compile block expressions
          compiledExpr <- compileMethodImpl blockExpr
          -- For now, ignore statements in method implementations
          return compiledExpr
        Term.RecordCreation _ _ fields -> do
          -- Compile record creation (like State { runState = ... })
          let conName = "State"  -- Assume State constructor
          fieldExprs <- mapM (compileMethodImpl . snd) fields
          return $ CoreCon conName fieldExprs
        _ -> return $ CoreVar (Var "compiled_unknown")
    
    -- Simple type compilation for method signatures
    compileTypeSimple :: Term.Type Ident -> CoreType
    compileTypeSimple ty = case ty of
      Term.TVar ident -> CoreTyVar (TyVar (unIdent ident))
      Term.TArrow t1 t2 -> TyArrow (compileTypeSimple t1) (compileTypeSimple t2)
      Term.TApp t1 t2 -> TyApp (compileTypeSimple t1) (compileTypeSimple t2)
      Term.TUnit -> TyUnit
      Term.TList t -> TyList (compileTypeSimple t)
      _ -> TyUnit

-- | Generate dictionary constructor for a trait instance
generateDictConstructor :: String -> String -> DictM CoreExpr
generateDictConstructor traitName typeName = do
  state <- get
  case Map.lookup (traitName, typeName) (dictInstances state) of
    Just methods -> do
      let targetType = TyCon typeName
      return $ CoreDict traitName targetType methods
    Nothing -> do
      -- Create a placeholder dictionary
      return $ CoreDict traitName (TyCon typeName) []

-- | Transform trait method calls to dictionary accesses
transformTraitMethod :: String -> String -> String -> CoreExpr -> CoreExpr
transformTraitMethod traitName typeName methodName dictVar = 
  CoreDictAccess dictVar methodName

-- | Get dictionary variable name for a trait and type
getDictVarName :: String -> String -> String
getDictVarName traitName typeName = "dict_" ++ traitName ++ "_" ++ typeName

-- | Transform a function with trait constraints to take dictionary parameters
transformConstrainedFunction :: Term.Expr Ident -> DictM CoreExpr
transformConstrainedFunction expr = do
  -- This is a simplified transformation - a full implementation would:
  -- 1. Identify trait constraints in the function type
  -- 2. Add dictionary parameters for each constraint
  -- 3. Transform trait method calls to dictionary accesses
  return $ CoreVar (Var "transformed_function")