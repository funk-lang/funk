module Funk.Fmt where

import Data.List
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM)
import Funk.Parser (parseTopLevel, PBinding(..))
import Funk.Term
import Funk.Token
import Text.Parsec (ParseError)

-- Simple error formatting
showParseErrorPretty :: ParseError -> String -> String
showParseErrorPretty err _ = show err

-- Format a file or directory with the given options
formatFile :: FmtOptions -> IO ()
formatFile opts = do
  isDir <- doesDirectoryExist (fmtFile opts)
  if isDir
    then formatDirectory opts
    else formatSingleFile opts

-- Format a single file
formatSingleFile :: FmtOptions -> IO ()
formatSingleFile opts = do
  exists <- doesFileExist (fmtFile opts)
  if not exists
    then putStrLn $ "Error: File not found: " ++ fmtFile opts
    else do
      content <- readFile (fmtFile opts)
      let result = tokenize content >>= parseTopLevel
      case result of
        Left err -> putStrLn $ "Parse error in " ++ fmtFile opts ++ ":\n" ++ showParseErrorPretty err content
        Right block -> do
          let formatted = formatBlock block
          if fmtInPlace opts
            then do
              writeFile (fmtFile opts) formatted
              putStrLn $ "Formatted: " ++ fmtFile opts
            else putStrLn formatted

-- Format all .funk files in a directory
formatDirectory :: FmtOptions -> IO ()
formatDirectory opts = do
  funkFiles <- findFunkFiles (fmtFile opts)
  if null funkFiles
    then putStrLn $ "No .funk files found in directory: " ++ fmtFile opts
    else do
      putStrLn $ "Found " ++ show (length funkFiles) ++ " .funk files in " ++ fmtFile opts
      mapM_ formatSingleFileInDir funkFiles
  where
    formatSingleFileInDir :: FilePath -> IO ()
    formatSingleFileInDir filePath = do
      content <- readFile filePath
      let result = tokenize content >>= parseTopLevel
      case result of
        Left err -> putStrLn $ "Parse error in " ++ filePath ++ ":\n" ++ showParseErrorPretty err content
        Right block -> do
          let formatted = formatBlock block
          if fmtInPlace opts
            then do
              writeFile filePath formatted
              putStrLn $ "Formatted: " ++ filePath
            else do
              putStrLn $ "=== " ++ filePath ++ " ==="
              putStrLn formatted
              putStrLn ""

-- Options for the format command
data FmtOptions = FmtOptions
  { fmtFile :: FilePath     -- File or directory to format
  , fmtInPlace :: Bool      -- Whether to modify files in place
  } deriving (Show)

-- Main formatting function
formatBlock :: Block PBinding -> String
formatBlock block = prettifyBlock block

-- Simple pretty printing function for blocks
prettifyBlock :: Block PBinding -> String
prettifyBlock (Block stmts expr) =
  let formattedStmts = map prettifyStmt stmts
      stmtsStr = intercalate "\n" $ addSensibleSpacing formattedStmts
      exprStr = case expr of
        PrimUnit _ -> ""
        _ -> prettifyExpr expr
  in if null exprStr then stmtsStr ++ "\n" else stmtsStr ++ "\n" ++ exprStr

-- Add sensible spacing between declarations
addSensibleSpacing :: [String] -> [String]
addSensibleSpacing [] = []
addSensibleSpacing [x] = [x]
addSensibleSpacing (x:y:xs) =
  if needsSpacing x y
    then x : "" : addSensibleSpacing (y:xs)
    else x : addSensibleSpacing (y:xs)
  where
    needsSpacing prev curr =
      (isMajorDecl prev && isMajorDecl curr) ||
      (isMajorDecl prev && not (isMajorDecl curr)) ||
      (not (isMajorDecl prev) && isMajorDecl curr)
    
    isMajorDecl stmt = 
      any (`isPrefixOf` stmt) ["data ", "trait ", "instance "]

-- Format statements with simple string-based approach
prettifyStmt :: Stmt PBinding -> String
prettifyStmt (Let _ (PBinding (Located _ (Ident name))) _ expr) =
  "let " ++ name ++ " = " ++ prettifyExpr expr ++ ";"
prettifyStmt (PubLet _ (PBinding (Located _ (Ident name))) _ expr) =
  "pub let " ++ name ++ " = " ++ prettifyExpr expr ++ ";"
prettifyStmt (Data _ constructors) =
  "data " ++ formatConstructors constructors
  where
    formatConstructors [(Ident cname, ty)] = cname ++ " = " ++ prettifyType ty
    formatConstructors xs = intercalate " | " $ map (\(Ident cname, ty) -> cname ++ " " ++ prettifyType ty) xs
prettifyStmt (PubData _ constructors) =
  "pub data " ++ formatConstructors constructors
  where
    formatConstructors [(Ident cname, ty)] = cname ++ " = " ++ prettifyType ty
    formatConstructors xs = intercalate " | " $ map (\(Ident cname, ty) -> cname ++ " " ++ prettifyType ty) xs
prettifyStmt (Trait name vars methods) =
  "trait " ++ prettifyTypeVar name ++ " " ++ formatTraitVars vars ++ " {\n" ++ formatTraitMethods methods ++ "\n}"
  where
    formatTraitVars [] = ""
    formatTraitVars [var] = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatTraitVars vs = intercalate " " $ map (\v -> "(" ++ prettifyTypeVar v ++ " :: * -> *)") vs
    formatTraitMethods [] = ""
    formatTraitMethods [method] = "  " ++ formatTraitMethod method
    formatTraitMethods ms = intercalate ",\n" (map (("  " ++) . formatTraitMethod) ms)
    formatTraitMethod (Ident mname, ty) = mname ++ ": " ++ prettifyType ty
prettifyStmt (PubTrait name vars methods) =
  "pub trait " ++ prettifyTypeVar name ++ " " ++ formatTraitVars vars ++ " {\n" ++ formatTraitMethods methods ++ "\n}"
  where
    formatTraitVars [] = ""
    formatTraitVars [var] = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatTraitVars vs = intercalate " " $ map (\v -> "(" ++ prettifyTypeVar v ++ " :: * -> *)") vs
    formatTraitMethods [] = ""
    formatTraitMethods [method] = "  " ++ formatTraitMethod method
    formatTraitMethods ms = intercalate ",\n" (map (("  " ++) . formatTraitMethod) ms)
    formatTraitMethod (Ident mname, ty) = mname ++ ": " ++ prettifyType ty
prettifyStmt (TraitWithKinds name vars methods) =
  "trait " ++ prettifyTypeVar name ++ " " ++ formatKindedVars vars ++ " {\n" ++ formatTraitMethods methods ++ "\n}"
  where
    formatKindedVars [] = ""
    formatKindedVars vs = intercalate " " $ map formatVarWithKind vs
    formatVarWithKind (var, Nothing) = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatVarWithKind (var, Just kind) = "(" ++ prettifyTypeVar var ++ " :: " ++ prettifyKind kind ++ ")"
    formatTraitMethods [] = ""
    formatTraitMethods [method] = "  " ++ formatTraitMethod method
    formatTraitMethods ms = intercalate ",\n" (map (("  " ++) . formatTraitMethod) ms)
    formatTraitMethod (Ident mname, ty) = mname ++ ": " ++ prettifyType ty
prettifyStmt (PubTraitWithKinds name vars methods) =
  "pub trait " ++ prettifyTypeVar name ++ " " ++ formatKindedVars vars ++ " {\n" ++ formatTraitMethods methods ++ "\n}"
  where
    formatKindedVars [] = ""
    formatKindedVars vs = intercalate " " $ map formatVarWithKind vs
    formatVarWithKind (var, Nothing) = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatVarWithKind (var, Just kind) = "(" ++ prettifyTypeVar var ++ " :: " ++ prettifyKind kind ++ ")"
    formatTraitMethods [] = ""
    formatTraitMethods [method] = "  " ++ formatTraitMethod method
    formatTraitMethods ms = intercalate ",\n" (map (("  " ++) . formatTraitMethod) ms)
    formatTraitMethod (Ident mname, ty) = mname ++ ": " ++ prettifyType ty
prettifyStmt (Impl traitName vars ty methods) =
  "instance " ++ prettifyTypeVar traitName ++ " " ++ formatImplVars vars ++ prettifyType ty ++ " = {" ++ formatImplMethods methods ++ "}"
  where
    formatImplVars [] = ""
    formatImplVars vs = "forall " ++ intercalate " " (map prettifyTypeVar vs) ++ " . "
    formatImplMethods [] = ""
    formatImplMethods [method] = 
      let formatted = formatImplMethod method
      in if isComplexMethod formatted then "\n  " ++ formatted ++ "\n" else formatted
    formatImplMethods ms = 
      let formattedMethods = map formatImplMethod ms
          hasComplexMethod = any isComplexMethod formattedMethods
      in if hasComplexMethod
         then "\n  " ++ intercalate ",\n  " formattedMethods ++ "\n"
         else intercalate ", " formattedMethods
    formatImplMethod (Ident mname, expr) = 
      let exprStr = prettifyExpr expr
      in mname ++ " = " ++ exprStr
    isComplexMethod formatted = 
      length formatted > 60 || 
      '\n' `elem` formatted ||  
      countWords formatted > 8  
    countWords = length . words
prettifyStmt (DataForall name vars fields) =
  "data " ++ prettifyTypeVar name ++ " " ++ intercalate " " (map prettifyTypeVar vars) ++ " = {" ++ formatDataFields fields ++ "}"
  where
    formatDataFields [] = ""
    formatDataFields [field] = formatDataField field
    formatDataFields fs = intercalate ", " (map formatDataField fs)
    formatDataField (Ident fname, ty) = fname ++ ": " ++ prettifyType ty
prettifyStmt (PubDataForall name vars fields) =
  "pub data " ++ prettifyTypeVar name ++ " " ++ intercalate " " (map prettifyTypeVar vars) ++ " = {" ++ formatDataFields fields ++ "}"
  where
    formatDataFields [] = ""
    formatDataFields [field] = formatDataField field
    formatDataFields fs = intercalate ", " (map formatDataField fs)
    formatDataField (Ident fname, ty) = fname ++ ": " ++ prettifyType ty
prettifyStmt (Use (ModulePath path) items) =
  "use " ++ intercalate "." (map (\(Ident i) -> i) path) ++ if null items then ".*;" else " {" ++ intercalate ", " (map (\(Ident i) -> i) items) ++ "};"
prettifyStmt (UseAll (ModulePath path)) =
  "use " ++ intercalate "." (map (\(Ident i) -> i) path) ++ ".*;"
prettifyStmt _ = "-- unsupported statement"

-- Simple type formatting
prettifyType :: Show a => Type a -> String
prettifyType (TVar var) = show var
prettifyType (TForall var body) = 
  let (vars, finalBody) = collectForallsLocal [var] body
  in "forall " ++ unwords (map show vars) ++ " . " ++ prettifyType finalBody
  where
    collectForallsLocal acc (TForall v b) = collectForallsLocal (acc ++ [v]) b
    collectForallsLocal acc b = (acc, b)
prettifyType (TArrow arg ret) = "(" ++ prettifyType arg ++ " -> " ++ prettifyType ret ++ ")"
prettifyType (TApp f arg) = prettifyType f ++ " " ++ prettifyType arg
prettifyType TUnit = "()"
prettifyType TString = "String"
prettifyType TInt = "Int"
prettifyType TBool = "Bool"
prettifyType (TList t) = "[" ++ prettifyType t ++ "]"
prettifyType (TIO t) = "#IO " ++ prettifyType t
prettifyType ty = show ty

prettifyTypeVar :: Show a => a -> String
prettifyTypeVar var = show var

prettifyKind :: Show a => Kind a -> String
prettifyKind KStar = "*"
prettifyKind (KArrow k1 k2) = prettifyKindAsArg k1 ++ " -> " ++ prettifyKind k2
prettifyKind (KVar var) = show var

prettifyKindAsArg :: Show a => Kind a -> String
prettifyKindAsArg k@(KArrow _ _) = "(" ++ prettifyKind k ++ ")"
prettifyKindAsArg k = prettifyKind k

-- Simple expression formatting
prettifyExpr :: Expr PBinding -> String
prettifyExpr (Var _ (PBinding (Located _ (Ident name)))) = name
prettifyExpr (QualifiedVar _ (ModulePath path) (PBinding (Located _ (Ident name)))) = 
  intercalate "." (map (\(Ident i) -> i) path) ++ "." ++ name
prettifyExpr (Lam _ (PBinding (Located _ (Ident arg))) _ body) =
  case body of
    Lam _ (PBinding (Located _ (Ident arg2))) _ body2 -> 
      "\\" ++ arg ++ " " ++ arg2 ++ " -> " ++ prettifyExpr body2
    _ -> "\\" ++ arg ++ " -> " ++ prettifyExpr body
prettifyExpr (App _ func arg) = prettifyExpr func ++ " " ++ prettifyExprAsArg arg
prettifyExpr (TyApp _ expr _) = prettifyExpr expr
prettifyExpr (BlockExpr _ block) = "{" ++ prettifyBlock block ++ "}"
prettifyExpr (RecordCreation _ expr fields) =
  let formattedFields = map showCreationField fields
      hasComplexField = any isComplexField formattedFields
      exprStr = prettifyExpr expr
  in if hasComplexField
     then exprStr ++ " {\n    " ++ intercalate ",\n    " formattedFields ++ "\n  }"
     else exprStr ++ " {" ++ intercalate ", " formattedFields ++ "}"
  where
    showCreationField (Ident fname, fieldExpr) = 
      let exprStr = prettifyExpr fieldExpr
          indentedExpr = if '\n' `elem` exprStr
                        then case lines exprStr of
                               [] -> exprStr
                               (firstLine:restLines) -> 
                                 let indentedRest = map ("  " ++) restLines
                                 in unlines (firstLine : indentedRest)
                        else exprStr
      in fname ++ " = " ++ indentedExpr
    isComplexField formatted = 
      length formatted > 40 || 
      '\n' `elem` formatted ||
      length (words formatted) > 6
prettifyExpr (TraitMethod _ _ _ _ (Ident name)) = name
prettifyExpr (PrimUnit _) = "#Unit"
prettifyExpr (PrimString _ s) = show s
prettifyExpr (PrimInt _ i) = show i
prettifyExpr (PrimTrue _) = "#true"
prettifyExpr (PrimFalse _) = "#false"
prettifyExpr (PrimNil _ _) = "#Nil"
prettifyExpr (PrimCons _ _ headExpr tailExpr) = "#Cons " ++ prettifyExprAsArg headExpr ++ " " ++ prettifyExprAsArg tailExpr
prettifyExpr (PrimIfThenElse _ cond then' else') = 
  "#ifThenElse " ++ prettifyExprAsArg cond ++ "\n  " ++ prettifyExprAsArg then' ++ "\n  " ++ prettifyExprAsArg else'
prettifyExpr (PrimBindIO _ io func) = "#bindIO " ++ prettifyExprAsArg io ++ " " ++ prettifyExprAsArg func
prettifyExpr (PrimPrint _ arg) = "#print " ++ prettifyExprAsArg arg
prettifyExpr (PrimIntEq _ left right) = "#intEq " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimIntSub _ left right) = "#intSub " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimStringEq _ left right) = "#stringEq " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimStringConcat _ left right) = "#stringConcat " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimPureIO _ arg) = "#pureIO " ++ prettifyExprAsArg arg
prettifyExpr (PrimFmapIO _ func io) = "#fmapIO " ++ prettifyExprAsArg func ++ " " ++ prettifyExprAsArg io
prettifyExpr (PrimApplyIO _ func io) = "#applyIO " ++ prettifyExprAsArg func ++ " " ++ prettifyExprAsArg io
prettifyExpr (PrimExit _ arg) = "#exit " ++ prettifyExprAsArg arg
-- Curried primitives
prettifyExpr (PrimBindIOValue _) = "#bindIO"
prettifyExpr (PrimIfThenElseValue _) = "#ifThenElse"
prettifyExpr (PrimPrintValue _) = "#print"
prettifyExpr (PrimIntEqValue _) = "#intEq"
prettifyExpr (PrimIntSubValue _) = "#intSub"
prettifyExpr (PrimStringEqValue _) = "#stringEq"
prettifyExpr (PrimStringConcatValue _) = "#stringConcat"
prettifyExpr (PrimPureIOValue _) = "#pureIO"
prettifyExpr (PrimFmapIOValue _) = "#fmapIO"
prettifyExpr (PrimApplyIOValue _) = "#applyIO"
prettifyExpr (PrimExitValue _) = "#exit"
prettifyExpr _ = "-- unsupported expression"

-- Helper function for adding parentheses when needed
prettifyExprAsArg :: Expr PBinding -> String
prettifyExprAsArg expr = 
  case expr of
    App _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    Lam _ _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    _ -> prettifyExpr expr

-- Find .funk files recursively
findFunkFiles :: FilePath -> IO [FilePath]
findFunkFiles path = do
  isDir <- doesDirectoryExist path
  if isDir
    then do
      entries <- listDirectory path
      allFiles <- forM entries $ \entry -> do
        let fullPath = path </> entry
        findFunkFiles fullPath
      return $ concat allFiles
    else do
      exists <- doesFileExist path
      if exists && takeExtension path == ".funk"
        then return [path]
        else return []

-- Expand input paths to include all .funk files from directories
expandInputPaths :: [FilePath] -> IO (Either String [FilePath])
expandInputPaths paths = do
  results <- forM paths $ \path -> do
    isDir <- doesDirectoryExist path
    if isDir
      then do
        files <- findFunkFiles path
        return $ Right files
      else do
        exists <- doesFileExist path
        if exists
          then return $ Right [path]
          else return $ Left $ "File not found: " ++ path
  let (errors, successes) = partitionEithers results
  if null errors
    then return $ Right $ concat successes
    else return $ Left $ unlines errors
  where
    partitionEithers :: [Either a b] -> ([a], [b])
    partitionEithers = foldr (either left right) ([], [])
      where
        left a ~(l, r) = (a:l, r)
        right a ~(l, r) = (l, a:r)
