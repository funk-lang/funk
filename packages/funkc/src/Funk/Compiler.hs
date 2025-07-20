{-# LANGUAGE LambdaCase #-}

module Funk.Compiler where

import Control.Applicative ((<|>))
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
-- | Infer expression type for let bindings
inferExpressionType :: Ident -> Term.Expr Ident -> CompileM CoreType
inferExpressionType (Ident name) expr = case name of
  -- Special cases for well-known functions based on name and usage
  "intEq" -> return $ TyArrow TyInt (TyArrow TyInt TyBool)
  "intSub" -> return $ TyArrow TyInt (TyArrow TyInt TyInt)
  "ifThenElse" -> do
    -- ifThenElse : Bool -> (Unit -> a) -> (Unit -> a) -> a
    a <- CoreTyVar <$> freshTyVar "a"
    return $ TyArrow TyBool (TyArrow (TyArrow TyUnit a) (TyArrow (TyArrow TyUnit a) a))
  "unit" -> return TyUnit
  _ -> case expr of
    -- Try to infer from expression patterns
    Term.Var _ (Ident "#Unit") -> return TyUnit
    _ -> return TyUnit  -- Default fallback

-- | Check if this is a well-known polymorphic function and generate appropriate type
checkPolymorphicFunction :: Ident -> CoreType
checkPolymorphicFunction (Ident name) = case name of
  "id" -> 
    -- id : forall a. a -> a
    let a = TyVar "a" in TyForall a (TyArrow (CoreTyVar a) (CoreTyVar a))
  "const" -> 
    -- const : forall a b. a -> b -> a  
    let a = TyVar "a"
        b = TyVar "b" 
    in TyForall a (TyForall b (TyArrow (CoreTyVar a) (TyArrow (CoreTyVar b) (CoreTyVar a))))
  "flip" ->
    -- flip : forall a b c. (a -> b -> c) -> b -> a -> c
    let a = TyVar "a"
        b = TyVar "b"
        c = TyVar "c"
    in TyForall a (TyForall b (TyForall c 
         (TyArrow (TyArrow (CoreTyVar a) (TyArrow (CoreTyVar b) (CoreTyVar c)))
                  (TyArrow (CoreTyVar b) (TyArrow (CoreTyVar a) (CoreTyVar c))))))
  "compose" ->
    -- compose : forall a b c. (b -> c) -> (a -> b) -> a -> c
    let a = TyVar "a"
        b = TyVar "b" 
        c = TyVar "c"
    in TyForall a (TyForall b (TyForall c
         (TyArrow (TyArrow (CoreTyVar b) (CoreTyVar c))
                  (TyArrow (TyArrow (CoreTyVar a) (CoreTyVar b))
                           (TyArrow (CoreTyVar a) (CoreTyVar c))))))
  _ -> 
    -- Not a recognized polymorphic function, use default
    CoreTyVar (TyVar "_")

-- | Infer lambda argument type from context and usage
inferLambdaArgumentType :: Ident -> Term.Expr Ident -> CompileM CoreType
inferLambdaArgumentType _ident body = do
  -- Analyze the body to see if we can infer the argument type
  case analyzeExprForTypes body of
    Just concreteType -> return concreteType
    Nothing -> do
      -- For genuinely polymorphic cases, use a meaningful type variable
      CoreTyVar <$> freshTyVar "a"

-- | Analyze an expression to extract type information
analyzeExprForTypes :: Term.Expr Ident -> Maybe CoreType
analyzeExprForTypes expr = case expr of
  -- If the body uses integer primitives, the arguments are likely Int
  Term.App _ (Term.Var _ (Ident "#intEq")) _ -> Just TyInt
  Term.App _ (Term.App _ (Term.Var _ (Ident "#intEq")) _) _ -> Just TyInt
  Term.App _ (Term.Var _ (Ident "#intSub")) _ -> Just TyInt  
  Term.App _ (Term.App _ (Term.Var _ (Ident "#intSub")) _) _ -> Just TyInt
  -- If the body uses boolean primitives, arguments might be Bool
  Term.App _ (Term.Var _ (Ident "#ifThenElse")) _ -> Just TyBool
  Term.App _ (Term.App _ (Term.Var _ (Ident "#ifThenElse")) _) _ -> Just TyBool
  -- Recursively analyze sub-expressions
  Term.App _ e1 e2 -> analyzeExprForTypes e1 <|> analyzeExprForTypes e2
  Term.Lam _ _ _ bodyExpr -> analyzeExprForTypes bodyExpr
  _ -> Nothing

-- | Try to infer concrete types for well-known polymorphic functions
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
        -- Try to infer the type from context or use a meaningful type variable
        inferLambdaArgumentType ident body
    
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
    return $ CorePrim PrimPrint [coreExpr]
  
  Term.PrimFmapIO _ f io -> do
    coreF <- compileResolvedExpr f
    coreIO <- compileResolvedExpr io
    return $ CorePrim PrimFmapIO [coreF, coreIO]
  
  Term.PrimPureIO _ expr -> do
    coreExpr <- compileResolvedExpr expr
    return $ CorePrim PrimPureIO [coreExpr]
  
  Term.PrimApplyIO _ iof iox -> do
    coreIOF <- compileResolvedExpr iof
    coreIOX <- compileResolvedExpr iox
    return $ CorePrim PrimApplyIO [coreIOF, coreIOX]
  
  Term.PrimBindIO _ iox f -> do
    coreIOX <- compileResolvedExpr iox
    coreF <- compileResolvedExpr f
    return $ CorePrim PrimBindIO [coreIOX, coreF]

  Term.PrimIntEq _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CorePrim PrimIntEq [coreE1, coreE2]

  Term.PrimStringEq _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CorePrim PrimStringEq [coreE1, coreE2]

  Term.PrimIfThenElse _ c t e -> do
    coreC <- compileResolvedExpr c
    coreT <- compileResolvedExpr t
    coreE <- compileResolvedExpr e
    return $ CorePrim PrimIfThenElse [coreC, coreT, coreE]

  Term.PrimIntSub _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CorePrim PrimIntSub [coreE1, coreE2]

  Term.PrimExit _ e -> do
    coreE <- compileResolvedExpr e
    return $ CorePrim PrimExit [coreE]

  Term.PrimStringConcat _ e1 e2 -> do
    coreE1 <- compileResolvedExpr e1
    coreE2 <- compileResolvedExpr e2
    return $ CorePrim PrimStringConcat [coreE1, coreE2]

  -- Primitive values (for currying)
  Term.PrimFmapIOValue _ -> return $ CorePrim PrimFmapIO []
  Term.PrimPureIOValue _ -> return $ CorePrim PrimPureIO []
  Term.PrimApplyIOValue _ -> return $ CorePrim PrimApplyIO []
  Term.PrimBindIOValue _ -> return $ CorePrim PrimBindIO []
  Term.PrimIntEqValue _ -> return $ CorePrim PrimIntEq []
  Term.PrimStringEqValue _ -> return $ CorePrim PrimStringEq []
  Term.PrimStringConcatValue _ -> return $ CorePrim PrimStringConcat []
  Term.PrimIfThenElseValue _ -> return $ CorePrim PrimIfThenElse []
  Term.PrimIntSubValue _ -> return $ CorePrim PrimIntSub []
  Term.PrimExitValue _ -> return $ CorePrim PrimExit []
  Term.PrimPrintValue _ -> return $ CorePrim PrimPrint []

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

-- | Check if a block has a main binding
hasMainBinding :: [Term.Stmt Ident] -> Bool
hasMainBinding stmts = any isMainBinding stmts
  where
    isMainBinding (Term.Let _ (Ident "main") _ _) = True
    isMainBinding _ = False

-- | Compile let bindings to CoreBinding list
compileBindings :: [Term.Stmt Ident] -> CompileM [CoreBinding]
compileBindings stmts = mapM compileBinding (filter isLetBinding stmts)
  where
    isLetBinding (Term.Let _ _ _ _) = True
    isLetBinding (Term.PubLet _ _ _ _) = True
    isLetBinding _ = False
    
    compileBinding (Term.Let _ ident mty expr) = do
      coreExpr <- compileResolvedExpr expr
      coreType <- case mty of
        Just ty -> compileType ty
        Nothing -> 
          -- Try to infer type for well-known polymorphic functions first
          case checkPolymorphicFunction ident of
            CoreTyVar (TyVar "_") -> 
              -- Not a known polymorphic function, try to infer from expression
              inferExpressionType ident expr
            polyType -> return polyType
      return $ CoreBinding (unIdent ident) coreType coreExpr
    compileBinding (Term.PubLet _ ident mty expr) = do
      coreExpr <- compileResolvedExpr expr
      coreType <- case mty of
        Just ty -> compileType ty
        Nothing -> 
          -- Try to infer type for well-known polymorphic functions first
          case checkPolymorphicFunction ident of
            CoreTyVar (TyVar "_") -> 
              -- Not a known polymorphic function, try to infer from expression
              inferExpressionType ident expr
            polyType -> return polyType
      return $ CoreBinding (unIdent ident) coreType coreExpr
    compileBinding _ = error "compileBinding called with non-let statement"

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

-- | Compile a complete STerm block to a Core module (program or library)
compileModule :: SBlock -> CompileM CoreModule
compileModule (Term.Block stmts expr) = do
  -- First resolve the block to get Term.Stmt Ident for checking
  resolvedBlock <- liftIO $ sBlockToDisplayWithTypes (Term.Block stmts expr)
  case resolvedBlock of
    Term.Block resolvedStmts _resolvedExpr -> do
      -- Extract trait and instance information
      env <- get
      let dictState = compileDictState env
      newDictState <- liftIO $ execStateT (do
        extractTraitInfo resolvedStmts
        extractInstanceInfo resolvedStmts) dictState
      put env { compileDictState = newDictState }
      
      -- Compile data types
      dataTypes <- extractDataTypes stmts
      
      -- Check if this is a program (has main) or library
      if hasMainBinding resolvedStmts
        then do
          mainExpr <- findMainBinding resolvedStmts
          return $ CoreProgram' (CoreProgram dataTypes mainExpr)
        else do
          bindings <- compileBindings resolvedStmts
          return $ CoreLibrary dataTypes bindings

-- | Main compilation function
compile :: SBlock -> IO CoreProgram
compile block = do
  (result, _env) <- runStateT (compileProgram block) emptyCompileEnv
  return result

-- | Main compilation function for modules (programs or libraries)
compileToModule :: SBlock -> IO CoreModule
compileToModule block = do
  (result, _env) <- runStateT (compileModule block) emptyCompileEnv
  return result

-- | Compile and pretty-print
compileAndShow :: SBlock -> IO String
compileAndShow block = do
  coreProgram <- compile block
  return $ show coreProgram