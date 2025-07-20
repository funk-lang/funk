{-# LANGUAGE LambdaCase #-}

module Funk.Dictionary where

import qualified Data.Map as Map
import Control.Monad.State
import Data.Maybe (fromMaybe)

import Funk.Core
import Funk.Term (Ident(..), unIdent)
import qualified Funk.Term as Term

-- | Trait method signature
data TraitMethod = TraitMethod
  { methodName :: String
  , methodType :: Term.Type Ident
  } deriving (Show, Eq)

-- | Trait definition
data TraitDef = TraitDef
  { traitName :: String
  , traitTypeParam :: String
  , traitMethods :: [TraitMethod]
  } deriving (Show, Eq)

-- | Instance definition  
data InstanceDef = InstanceDef
  { instanceTrait :: String
  , instanceType :: String
  , instanceMethods :: Map.Map String CoreExpr
  } deriving (Show, Eq)

-- | Dictionary transformation state
data DictState = DictState
  { dictTraits :: Map.Map String TraitDef
  , dictInstances :: Map.Map (String, String) InstanceDef  -- (trait, type) -> instance
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
      Term.Trait traitIdent _typeVars methods -> do
        let traitNameStr = unIdent traitIdent
        let traitMethods = map (\(methodIdent, methodTy) -> 
              TraitMethod (unIdent methodIdent) methodTy) methods
        let traitDef = TraitDef traitNameStr "f" traitMethods
        dictState <- get
        put dictState { dictTraits = Map.insert traitNameStr traitDef (dictTraits dictState) }
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
        let methodMap = Map.fromList $ zip (map (unIdent . fst) methods) methodImpls
        let instanceDef = InstanceDef {
              instanceTrait = traitNameStr,
              instanceType = instanceTypeStr,
              instanceMethods = methodMap
            }
        dictState <- get
        put dictState { dictInstances = Map.insert (traitNameStr, instanceTypeStr) instanceDef (dictInstances dictState) }
      _ -> return ()
    
    compileMethodImpl :: Term.Expr Ident -> DictM CoreExpr
    compileMethodImpl expr = do
      -- Properly compile method implementations
      case expr of
        Term.Var _ ident -> return $ CoreVar (Var (unIdent ident))
        Term.Lam _ param mtype body -> do
          -- Compile lambda with proper type handling
          let paramVar = Var (unIdent param)
          let argType = maybe TyUnit compileTypeSimple mtype
          bodyExpr <- compileMethodImpl body
          return $ CoreLam paramVar argType bodyExpr
        Term.App _ func arg -> do
          -- Compile function applications
          funcExpr <- compileMethodImpl func
          argExpr <- compileMethodImpl arg
          return $ CoreApp funcExpr argExpr
        Term.BlockExpr _ (Term.Block _ blockExpr') -> do
          -- Compile block expressions
          -- For now, ignore statements in method implementations
          compileMethodImpl blockExpr'
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
  dictState <- get
  case Map.lookup (traitName, typeName) (dictInstances dictState) of
    Just instanceDef -> do
      let targetType = TyCon typeName
      let methods = Map.elems (instanceMethods instanceDef)
      return $ CoreDict traitName targetType methods
    Nothing -> do
      -- Create a placeholder dictionary
      return $ CoreDict traitName (TyCon typeName) []

-- | Transform trait method calls to dictionary accesses
transformTraitMethod :: String -> String -> String -> CoreExpr -> CoreExpr
transformTraitMethod _ _ methodName dictVar = 
  CoreDictAccess dictVar methodName

-- | Get dictionary variable name for a trait and type
getDictVarName :: String -> String -> String
getDictVarName traitName typeName = "dict_" ++ traitName ++ "_" ++ typeName

-- | Transform a function with trait constraints to take dictionary parameters
transformConstrainedFunction :: Term.Expr Ident -> DictM CoreExpr
transformConstrainedFunction _ = do
  -- This is a simplified transformation - a full implementation would:
  -- 1. Identify trait constraints in the function type
  -- 2. Add dictionary parameters for each constraint
  -- 3. Transform trait method calls to dictionary accesses
  return $ CoreVar (Var "transformed_function")