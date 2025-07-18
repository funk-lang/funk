{-# LANGUAGE LambdaCase #-}

module Funk.Compiler where

import Control.Monad.State
import Data.Foldable (foldrM)
import qualified Data.Map as Map

import Funk.Core
import Funk.STerm
import Funk.Term (Ident(..), unIdent)
import qualified Funk.Term as Term
import Funk.Dictionary

-- | Compilation environment
data CompileEnv = CompileEnv
  { compileVarCounter :: Int
  , compileTyVarCounter :: Int
  , compileVarMap :: Map.Map Ident Funk.Core.Var
  , compileTyVarMap :: Map.Map Ident TyVar
  , compileDictState :: DictState
  } deriving (Show)

type CompileM = StateT CompileEnv IO

-- | Initial compilation environment
emptyCompileEnv :: CompileEnv
emptyCompileEnv = CompileEnv 0 0 Map.empty Map.empty emptyDictState

-- | Generate a fresh variable
freshVar :: String -> CompileM Funk.Core.Var
freshVar prefix = do
  env <- get
  let counter = compileVarCounter env
  put env { compileVarCounter = counter + 1 }
  return $ Funk.Core.Var (prefix ++ show counter)

-- | Generate a fresh type variable
freshTyVar :: String -> CompileM TyVar
freshTyVar prefix = do
  env <- get
  let counter = compileTyVarCounter env
  put env { compileTyVarCounter = counter + 1 }
  return $ TyVar (prefix ++ show counter)

-- | Convert Ident to Var, creating a mapping if needed
identToVar :: Ident -> CompileM Funk.Core.Var
identToVar ident = do
  env <- get
  case Map.lookup ident (compileVarMap env) of
    Just var -> return var
    Nothing -> do
      let var = Funk.Core.Var (unIdent ident)
      put env { compileVarMap = Map.insert ident var (compileVarMap env) }
      return var

-- | Convert Ident to TyVar, creating a mapping if needed
identToTyVar :: Ident -> CompileM TyVar
identToTyVar ident = do
  env <- get
  case Map.lookup ident (compileTyVarMap env) of
    Just tyvar -> return tyvar
    Nothing -> do
      let tyvar = TyVar (unIdent ident)
      put env { compileTyVarMap = Map.insert ident tyvar (compileTyVarMap env) }
      return tyvar

-- | Compile a type from the surface language to core
compileType :: Term.Type Ident -> CompileM CoreType
compileType = \case
  Term.TVar ident -> CoreTyVar <$> identToTyVar ident
  Term.TArrow t1 t2 -> TyArrow <$> compileType t1 <*> compileType t2
  Term.TForall ident t -> do
    tyvar <- identToTyVar ident
    coreType <- compileType t
    return $ TyForall tyvar coreType
  Term.TApp t1 t2 -> TyApp <$> compileType t1 <*> compileType t2
  Term.TUnit -> return TyUnit
  Term.TString -> return TyString
  Term.TInt -> return TyInt
  Term.TBool -> return TyBool
  Term.TList t -> TyList <$> compileType t
  Term.TIO t -> TyIO <$> compileType t
  Term.TConstraint _traitName _typeVars targetType _bodyType -> do
    -- For now, compile trait constraints to their target type
    -- In a full implementation, this would handle dictionary passing
    compileType targetType

-- | Compile an STerm type to core
compileSType :: SType -> CompileM CoreType
compileSType stype = do
  displayType <- liftIO $ sTypeToDisplay stype
  compileType displayType

-- | Compile an expression from STerms to Core
compileExpr :: SExpr -> CompileM CoreExpr
compileExpr sexpr = do
  -- First resolve the SExpr to display form to get properly resolved trait methods
  resolvedExpr <- liftIO $ sExprToDisplayWithTypes sexpr
  compileResolvedExpr resolvedExpr

-- | Compile a resolved expression (from display form) to Core
compileResolvedExpr :: Term.Expr Ident -> CompileM CoreExpr
compileResolvedExpr = \case
  Term.Var _ ident -> do
    var <- identToVar ident
    return $ CoreVar var
  
  Term.QualifiedVar _ _modPath ident -> do
    -- For now, treat qualified vars as regular vars (full module resolution TBD)
    var <- identToVar ident
    return $ CoreVar var
  
  Term.Lam _ ident mty body -> do
    var <- identToVar ident
    
    -- Get the argument type
    argType <- case mty of
      Just ty -> compileType ty
      Nothing -> do
        -- Use a fresh type variable for untyped lambdas
        CoreTyVar <$> freshTyVar "a"
    
    coreBody <- compileResolvedExpr body
    return $ CoreLam var argType coreBody
  
  Term.App _ e1 e2 -> do
    core1 <- compileResolvedExpr e1
    core2 <- compileResolvedExpr e2
    return $ CoreApp core1 core2
  
  Term.TyApp _ expr ty -> do
    coreExpr <- compileResolvedExpr expr
    coreType <- compileType ty
    return $ CoreTyApp coreExpr coreType
  
  Term.BlockExpr _ block -> compileResolvedBlock block
  
  Term.TraitMethod _ traitName _typeArgs targetType methodName -> do
    -- For trait methods, we generate a dictionary access
    _traitName' <- identToVar traitName
    targetType' <- compileType targetType
    let targetTypeName = case targetType' of
          CoreTyVar (TyVar name) -> 
            -- If it's still a type variable, try to resolve it from context
            if take 1 name == "t" then "State" else name  -- Heuristic: assume State for now
          TyCon name -> name
          TyApp (TyCon name) _ -> name
          TyApp (CoreTyVar (TyVar name)) _ -> name
          _ -> "Unknown"
    
    let traitNameStr = unIdent traitName
    let methodNameStr = unIdent methodName
    
    -- Generate dictionary constructor for this trait/type combination
    env <- get
    let dictState = compileDictState env
    dictExpr <- liftIO $ evalStateT (generateDictConstructor traitNameStr targetTypeName) dictState
    
    -- Create dictionary access expression
    return $ CoreDictAccess dictExpr methodNameStr
  
  Term.PrimUnit _ -> return CoreUnit
  
  Term.PrimString _ s -> return $ CoreString s
  
  Term.PrimInt _ i -> return $ CoreInt i
  
  Term.PrimTrue _ -> return CoreTrue
  
  Term.PrimFalse _ -> return CoreFalse
  
  Term.PrimNil _ ty -> do
    coreType <- compileType ty
    return $ CoreNil coreType
  
  Term.PrimCons _ ty headExpr tailExpr -> do
    coreType <- compileType ty
    coreHead <- compileResolvedExpr headExpr
    coreTail <- compileResolvedExpr tailExpr
    return $ CoreCons coreType coreHead coreTail
  
  Term.RecordType _ _var fields -> do
    -- For records, create a constructor application
    -- This is a simplified compilation - a full implementation would handle records properly
    let conName = "Record" ++ show (length fields)
    return $ CoreCon conName []
  
  Term.RecordCreation _ _expr fields -> do
    -- Compile record creation to constructor application
    let conName = "Record" ++ show (length fields)
    fieldExprs <- mapM (compileResolvedExpr . snd) fields
    return $ CoreCon conName fieldExprs
  
  Term.PrimPrint _ expr -> do
    coreExpr <- compileResolvedExpr expr
    return $ CorePrint coreExpr
  
  Term.PrimFmapIO _ f io -> do
    coreF <- compileResolvedExpr f
    coreIO <- compileResolvedExpr io
    return $ CoreFmapIO coreF coreIO
  
  Term.PrimPureIO _ expr -> do
    coreExpr <- compileResolvedExpr expr
    return $ CorePureIO coreExpr
  
  Term.PrimApplyIO _ iof iox -> do
    coreIOF <- compileResolvedExpr iof
    coreIOX <- compileResolvedExpr iox
    return $ CoreApplyIO coreIOF coreIOX
  
  Term.PrimBindIO _ iox f -> do
    coreIOX <- compileResolvedExpr iox
    coreF <- compileResolvedExpr f
    return $ CoreBindIO coreIOX coreF

  Term.PrimIntEq _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CoreIntEq coreE1 coreE2

  Term.PrimStringEq _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CoreStringEq coreE1 coreE2

  Term.PrimIfThenElse _ c t e -> do
    coreC <- compileResolvedExpr c
    coreT <- compileResolvedExpr t
    coreE <- compileResolvedExpr e
    return $ CoreIfThenElse coreC coreT coreE

  Term.PrimIntSub _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CoreIntSub coreE1 coreE2

  Term.PrimExit _ e -> do
    coreE <- compileResolvedExpr e
    return $ CoreExit coreE

-- | Compile a block (sequence of statements) to core
compileBlock :: SBlock -> CompileM CoreExpr
compileBlock sblock = do
  -- First resolve the block to display form
  resolvedBlock <- liftIO $ sBlockToDisplayWithTypes sblock
  compileResolvedBlock resolvedBlock

-- | Compile a resolved block (from display form) to core
compileResolvedBlock :: Term.Block Ident -> CompileM CoreExpr
compileResolvedBlock (Term.Block stmts expr) = do
  coreExpr <- compileResolvedExpr expr
  foldrM compileResolvedStmt coreExpr stmts

-- | Compile a statement, threading it through the rest of the computation
compileStmt :: SStmt -> CoreExpr -> CompileM CoreExpr
compileStmt stmt rest = do
  -- First resolve the statement to display form
  resolvedStmt <- liftIO $ sStmtToDisplay stmt
  compileResolvedStmt resolvedStmt rest

-- | Compile a resolved statement, threading it through the rest of the computation
compileResolvedStmt :: Term.Stmt Ident -> CoreExpr -> CompileM CoreExpr
compileResolvedStmt stmt rest = case stmt of
  Term.Let _ ident _mty body -> do
    var <- identToVar ident
    coreBody <- compileResolvedExpr body
    return $ CoreLet var coreBody rest
  
  Term.Type _binding _ty -> 
    -- Type aliases don't generate runtime code
    return rest
  
  Term.Data _binding _fields -> do
    -- Data declarations don't generate runtime code here
    -- They would be handled at the program level
    return rest
  
  Term.DataForall _binding _vars _fields -> do
    -- Polymorphic data declarations
    return rest
  
  Term.Trait _binding _vars _methods -> do
    -- Trait declarations don't generate runtime code
    return rest
  
  Term.TraitWithKinds _binding _vars _methods -> do
    -- Trait declarations with kinds
    return rest
  
  Term.Impl _binding _vars _ty _methods -> do
    -- Instance implementations would generate dictionary definitions
    -- For now, we skip them
    return rest
  
  Term.PubLet _ ident _mty body -> do
    -- Same as Let but with pub visibility
    var <- identToVar ident
    coreBody <- compileResolvedExpr body
    return $ CoreLet var coreBody rest
  
  Term.PubType _binding _ty -> 
    -- Public type aliases don't generate runtime code
    return rest
  
  Term.PubData _binding _fields -> do
    -- Public data declarations
    return rest
  
  Term.PubDataForall _binding _vars _fields -> do
    -- Public polymorphic data declarations
    return rest
  
  Term.PubTrait _binding _vars _methods -> do
    -- Public trait declarations
    return rest
  
  Term.PubTraitWithKinds _binding _vars _methods -> do
    -- Public trait declarations with kinds
    return rest
  
  Term.Use _modPath _names -> do
    -- Import statements don't generate runtime code
    return rest
  
  Term.UseAll _modPath -> do
    -- Import all statements don't generate runtime code
    return rest
  
  Term.PubUse _modPath _names -> do
    -- Public re-export statements don't generate runtime code
    return rest
  
  Term.PubUseAll _modPath -> do
    -- Public re-export all statements don't generate runtime code
    return rest

-- | Extract data type definitions from statements
extractDataTypes :: [SStmt] -> CompileM [CoreDataType]
extractDataTypes stmts = do
  concat <$> mapM extractDataType stmts
  where
    extractDataType :: SStmt -> CompileM [CoreDataType]
    extractDataType = \case
      Term.Data binding fields -> do
        binding' <- liftIO $ sTBindingToIdent binding
        let name = unIdent binding'
        fieldTypes <- mapM (compileSType . snd) fields
        let _fieldNames = map (unIdent . fst) fields
        -- Create a single constructor with all fields
        return [CoreDataType name [] [(name, fieldTypes)]]
      
      Term.DataForall binding tyVars fields -> do
        binding' <- liftIO $ sTBindingToIdent binding
        tyVars' <- mapM (\tyVar -> liftIO (sTBindingToIdent tyVar) >>= identToTyVar . Ident . unIdent) tyVars
        let name = unIdent binding'
        fieldTypes <- mapM (compileSType . snd) fields
        return [CoreDataType name tyVars' [(name, fieldTypes)]]
      
      _ -> return []

-- | Find the main binding in the statements and compile it with proper context
findMainBinding :: [Term.Stmt Ident] -> CompileM CoreExpr
findMainBinding stmts = do
  case findMainStmt stmts of
    Just (mainBody, otherStmts) -> do
      -- Compile all the other statements first to build context
      mainExpr <- compileResolvedExpr mainBody
      foldrM compileResolvedStmt mainExpr otherStmts
    Nothing -> error "No main binding found in program"
  where
    findMainStmt :: [Term.Stmt Ident] -> Maybe (Term.Expr Ident, [Term.Stmt Ident])
    findMainStmt allStmts = go allStmts []
      where
        go [] _ = Nothing
        go (Term.Let _ (Ident "main") _ body : rest) acc = 
          Just (body, acc ++ rest)
        go (stmt : rest) acc = go rest (acc ++ [stmt])

-- | Compile a complete STerm block to a Core program
compileProgram :: SBlock -> CompileM CoreProgram
compileProgram (Term.Block stmts expr) = do
  -- First resolve the block to get Term.Stmt Ident for checking
  resolvedBlock <- liftIO $ sBlockToDisplayWithTypes (Term.Block stmts expr)
  case resolvedBlock of
    Term.Block resolvedStmts _resolvedExpr -> do
      -- The parser ensures top-level programs only contain statements with a unit placeholder
      -- No need to check the final expression since it's always unit from the parser
      
      -- Extract trait and instance information
      env <- get
      let dictState = compileDictState env
      newDictState <- liftIO $ execStateT (do
        extractTraitInfo resolvedStmts
        extractInstanceInfo resolvedStmts) dictState
      put env { compileDictState = newDictState }
      
      -- Compile data types
      dataTypes <- extractDataTypes stmts
      
      -- Look for main binding in the statements
      mainExpr <- findMainBinding resolvedStmts
      
      return $ CoreProgram dataTypes mainExpr

-- | Main compilation function
compile :: SBlock -> IO CoreProgram
compile block = do
  (result, _env) <- runStateT (compileProgram block) emptyCompileEnv
  return result

-- | Compile and pretty-print
compileAndShow :: SBlock -> IO String
compileAndShow block = do
  coreProgram <- compile block
  return $ show coreProgram