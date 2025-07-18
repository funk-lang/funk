module Funk.Fmt where

import Data.List
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM)
import Funk.Parser (parseTopLevel, PBinding(..))
import Funk.Term
import Funk.Token
import Text.Parsec (ParseError)

-- We'll need to import the colored error function from the main module
-- For now, let's define a simple version
showParseErrorPretty :: ParseError -> String -> String
showParseErrorPretty err _ = show err  -- Fallback to simple show for now

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

-- Advanced formatter that produces clean source code with line length limits
formatBlock :: Block PBinding -> String
formatBlock block = formatContent $ prettifyBlock block
  where
    formatContent content = 
      let lines' = lines content
          processedLines = map (wrapLine 80) lines'
          -- More permissive: only squash 3+ consecutive empty lines into 2
          spacedLines = squashExcessiveEmptyLines processedLines
      in unlines spacedLines
    
    -- Only squash 3+ consecutive empty lines, preserve 1-2 blank lines
    squashExcessiveEmptyLines :: [String] -> [String]
    squashExcessiveEmptyLines [] = []
    squashExcessiveEmptyLines lines' = go lines' 0
      where
        go [] _ = []
        go (x:xs) emptyCount
          | isEmptyLine x = 
              if emptyCount >= 2 
                then go xs emptyCount  -- Skip this empty line (already have 2)
                else x : go xs (emptyCount + 1)
          | otherwise = x : go xs 0
    
    isEmptyLine :: String -> Bool
    isEmptyLine = null . dropWhile (==' ')
    
    -- Wrap lines that exceed the maximum length
    wrapLine :: Int -> String -> String
    wrapLine maxLen line
      | length line <= maxLen = line
      | otherwise = 
          let (prefix, suffix) = splitAt maxLen line
              lastSpace = lastIndexOf ' ' prefix
          in if lastSpace > 0
             then take lastSpace prefix ++ "\n  " ++ wrapLine maxLen (drop (lastSpace + 1) line)
             else line  -- Don't break if no good split point
    
    lastIndexOf :: Eq a => a -> [a] -> Int
    lastIndexOf x xs = case elemIndices x xs of
      [] -> -1
      indices -> last indices

-- Convert AST back to clean Funk source code
prettifyBlock :: Block PBinding -> String
prettifyBlock (Block stmts expr) =
  let formattedStmts = map prettifyStmt stmts
      -- Add sensible default spacing between declarations
      stmtsStr = intercalate "\n" $ addSensibleSpacing formattedStmts
      -- Only add the expression if it's not just a Unit
      exprStr = case expr of
        PrimUnit _ -> ""
        _ -> prettifyExpr expr
  in if null exprStr then stmtsStr ++ "\n" else stmtsStr ++ "\n" ++ exprStr

-- Add sensible spacing: blank lines between all major declarations (traits, instances, data types)
-- but not between simple let bindings
addSensibleSpacing :: [String] -> [String]
addSensibleSpacing [] = []
addSensibleSpacing [x] = [x]
addSensibleSpacing (x:y:xs) =
  if needsSpacing x y
    then x : "" : addSensibleSpacing (y:xs)
    else x : addSensibleSpacing (y:xs)
  where
    needsSpacing prev curr =
      -- Add spacing between any major declarations
      (isMajorDecl prev && isMajorDecl curr) ||
      -- Add spacing between major declarations and other statements
      (isMajorDecl prev && not (isMajorDecl curr)) ||
      (not (isMajorDecl prev) && isMajorDecl curr)
    
    isMajorDecl stmt = 
      any (`isPrefixOf` stmt) ["data ", "trait ", "instance "]

prettifyStmt :: Stmt PBinding -> String
prettifyStmt (Let _ (PBinding (Located _ (Ident name))) _ expr) =
  "let " ++ name ++ " = " ++ prettifyExpr expr ++ ";"
prettifyStmt (PubLet _ (PBinding (Located _ (Ident name))) _ expr) =
  "pub let " ++ name ++ " = " ++ prettifyExpr expr ++ ";"
prettifyStmt (Data _ constructors) =
  "data " ++ formatConstructors constructors
  where
    formatConstructors [(Ident name, ty)] = name ++ " = " ++ prettifyTypeSimple ty
    formatConstructors xs = intercalate " | " $ map (\(Ident name, ty) -> name ++ " " ++ prettifyTypeSimple ty) xs
prettifyStmt (PubData _ constructors) =
  "pub data " ++ formatConstructors constructors
  where
    formatConstructors [(Ident name, ty)] = name ++ " = " ++ prettifyTypeSimple ty
    formatConstructors xs = intercalate " | " $ map (\(Ident name, ty) -> name ++ " " ++ prettifyTypeSimple ty) xs
prettifyStmt (Trait name vars methods) =
  "trait " ++ prettifyTypeVar name ++ " " ++ formatVars vars ++ " {\n" ++ formatMethods methods ++ "\n}"
  where
    formatVars [] = ""
    formatVars [var] = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatVars vars = intercalate " " $ map (\v -> "(" ++ prettifyTypeVar v ++ " :: * -> *)") vars
    formatMethods [] = ""
    formatMethods [method] = "  " ++ formatMethod method
    formatMethods methods = intercalate ",\n" (map (("  " ++) . formatMethod) methods)
    formatMethod (Ident name, ty) = name ++ ": " ++ prettifyTypeSimple ty
prettifyStmt (PubTrait name vars methods) =
  "pub trait " ++ prettifyTypeVar name ++ " " ++ formatVars vars ++ " {\n" ++ formatMethods methods ++ "\n}"
  where
    formatVars [] = ""
    formatVars [var] = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatVars vars = intercalate " " $ map (\v -> "(" ++ prettifyTypeVar v ++ " :: * -> *)") vars
    formatMethods [] = ""
    formatMethods [method] = "  " ++ formatMethod method
    formatMethods methods = intercalate ",\n" (map (("  " ++) . formatMethod) methods)
    formatMethod (Ident name, ty) = name ++ ": " ++ prettifyTypeSimple ty
prettifyStmt (TraitWithKinds name vars methods) =
  "trait " ++ prettifyTypeVar name ++ " " ++ formatVarsWithKinds vars ++ " {\n" ++ formatMethods methods ++ "\n}"
  where
    formatVarsWithKinds [] = ""
    formatVarsWithKinds vars = intercalate " " $ map formatVarWithKind vars
    formatVarWithKind (var, Nothing) = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatVarWithKind (var, Just kind) = "(" ++ prettifyTypeVar var ++ " :: " ++ prettifyKind kind ++ ")"
    formatMethods [] = ""
    formatMethods [method] = "  " ++ formatMethod method
    formatMethods methods = intercalate ",\n" (map (("  " ++) . formatMethod) methods)
    formatMethod (Ident name, ty) = name ++ ": " ++ prettifyTypeSimple ty
prettifyStmt (PubTraitWithKinds name vars methods) =
  "pub trait " ++ prettifyTypeVar name ++ " " ++ formatVarsWithKinds vars ++ " {\n" ++ formatMethods methods ++ "\n}"
  where
    formatVarsWithKinds [] = ""
    formatVarsWithKinds vars = intercalate " " $ map formatVarWithKind vars
    formatVarWithKind (var, Nothing) = "(" ++ prettifyTypeVar var ++ " :: * -> *)"
    formatVarWithKind (var, Just kind) = "(" ++ prettifyTypeVar var ++ " :: " ++ prettifyKind kind ++ ")"
    formatMethods [] = ""
    formatMethods [method] = "  " ++ formatMethod method
    formatMethods methods = intercalate ",\n" (map (("  " ++) . formatMethod) methods)
    formatMethod (Ident name, ty) = name ++ ": " ++ prettifyTypeSimple ty
prettifyStmt (Impl traitName vars ty methods) =
  "instance " ++ prettifyTypeVar traitName ++ " " ++ formatVars vars ++ prettifyTypeSimple ty ++ " = {" ++ formatMethods methods ++ "}"
  where
    formatVars [] = ""
    formatVars vars = "forall " ++ intercalate " " (map prettifyTypeVar vars) ++ " . "
    formatMethods [] = ""
    formatMethods [method] = formatMethod method
    formatMethods methods = intercalate ", " (map formatMethod methods)
    formatMethod (Ident name, expr) = name ++ " = " ++ prettifyExpr expr
prettifyStmt (DataForall name vars fields) =
  "data " ++ prettifyTypeVar name ++ " " ++ intercalate " " (map prettifyTypeVar vars) ++ " = {" ++ formatFields fields ++ "}"
  where
    formatFields [] = ""
    formatFields [field] = formatField field
    formatFields fields = intercalate ", " (map formatField fields)
    formatField (Ident name, ty) = name ++ ": " ++ prettifyTypeSimple ty
prettifyStmt (PubDataForall name vars fields) =
  "pub data " ++ prettifyTypeVar name ++ " " ++ intercalate " " (map prettifyTypeVar vars) ++ " = {" ++ formatFields fields ++ "}"
  where
    formatFields [] = ""
    formatFields [field] = formatField field
    formatFields fields = intercalate ", " (map formatField fields)
    formatField (Ident name, ty) = name ++ ": " ++ prettifyTypeSimple ty
prettifyStmt (Use (ModulePath path) items) =
  "use " ++ intercalate "." (map (\(Ident i) -> i) path) ++ if null items then ".*;" else " {" ++ intercalate ", " (map (\(Ident i) -> i) items) ++ "};"
prettifyStmt (UseAll (ModulePath path)) =
  "use " ++ intercalate "." (map (\(Ident i) -> i) path) ++ ".*;"
prettifyStmt _ = "-- unsupported statement"  -- fallback

-- Helper functions for type formatting
prettifyTypeSimple :: Show a => Type a -> String
prettifyTypeSimple (TVar var) = show var
prettifyTypeSimple (TForall var body) = 
  let (vars, finalBody) = collectForalls [var] body
  in "forall " ++ unwords (map show vars) ++ " . " ++ prettifyTypeSimple finalBody
  where
    collectForalls acc (TForall v b) = collectForalls (acc ++ [v]) b
    collectForalls acc b = (acc, b)
prettifyTypeSimple (TArrow arg ret) = "(" ++ prettifyTypeSimple arg ++ " -> " ++ prettifyTypeSimple ret ++ ")"
prettifyTypeSimple (TApp f arg) = prettifyTypeSimple f ++ " " ++ prettifyTypeSimple arg
prettifyTypeSimple TUnit = "()"
prettifyTypeSimple TString = "String"
prettifyTypeSimple TInt = "Int"
prettifyTypeSimple TBool = "Bool"
prettifyTypeSimple (TList t) = "[" ++ prettifyTypeSimple t ++ "]"
prettifyTypeSimple (TIO t) = "#IO " ++ prettifyTypeSimple t
prettifyTypeSimple ty = show ty  -- Fallback for other types

prettifyTypeVar :: Show a => a -> String
prettifyTypeVar var = show var  -- Simplified for now

prettifyKind :: Show a => Kind a -> String
prettifyKind KStar = "*"
prettifyKind (KArrow k1 k2) = prettifyKindAsArg k1 ++ " -> " ++ prettifyKind k2
prettifyKind (KVar var) = show var
prettifyKind kind = show kind  -- Fallback

-- Helper function to add parentheses only when needed for kind expressions
prettifyKindAsArg :: Show a => Kind a -> String
prettifyKindAsArg k@(KArrow _ _) = "(" ++ prettifyKind k ++ ")"
prettifyKindAsArg k = prettifyKind k

prettifyExpr :: Expr PBinding -> String
prettifyExpr (Var _ (PBinding (Located _ (Ident name)))) = name
prettifyExpr (QualifiedVar _ (ModulePath path) (PBinding (Located _ (Ident name)))) = 
  intercalate "." (map (\(Ident i) -> i) path) ++ "." ++ name
prettifyExpr (Lam _ (PBinding (Located _ (Ident arg))) _ body) =
  case body of
    Lam _ (PBinding (Located _ (Ident arg2))) _ body2 -> 
      "\\" ++ arg ++ " " ++ arg2 ++ " -> " ++ prettifyExpr body2
    _ -> "\\" ++ arg ++ " -> " ++ prettifyExpr body
prettifyExpr (App _ func arg) =
  case func of
    -- Special case: if we're applying a second argument to #bindIO, treat it as one unit
    App _ (PrimBindIOValue _) firstArg -> "#bindIO " ++ prettifyExprAsArg firstArg ++ " " ++ prettifyExprAsArg arg
    -- Normal function application
    _ -> prettifyExpr func ++ " " ++ prettifyExprAsArg arg
prettifyExpr (TyApp _ expr _) = prettifyExpr expr  -- Skip type applications in output
prettifyExpr (BlockExpr _ block) =
  "{" ++ prettifyBlock block ++ "}"
prettifyExpr (RecordType _ _ fields) =
  "{" ++ intercalate ", " (map showField fields) ++ "}"
  where
    showField (Ident name, _) = name
prettifyExpr (RecordCreation _ expr fields) =
  prettifyExpr expr ++ " {" ++ intercalate ", " (map showField fields) ++ "}"
  where
    showField (Ident name, fieldExpr) = name ++ " = " ++ prettifyExpr fieldExpr
prettifyExpr (TraitMethod _ _ _ _ (Ident name)) = name
prettifyExpr (PrimUnit _) = "#Unit"
prettifyExpr (PrimString _ s) = show s
prettifyExpr (PrimInt _ i) = show i
prettifyExpr (PrimTrue _) = "#true"
prettifyExpr (PrimFalse _) = "#false"
prettifyExpr (PrimNil _ _) = "#Nil"
prettifyExpr (PrimCons _ _ headExpr tailExpr) = "#Cons " ++ prettifyExprAsArg headExpr ++ " " ++ prettifyExprAsArg tailExpr
prettifyExpr (PrimPrint _ arg) = "#print " ++ prettifyExprAsArg arg
prettifyExpr (PrimFmapIO _ func io) = "#fmapIO " ++ prettifyExprAsArg func ++ " " ++ prettifyExprAsArg io
prettifyExpr (PrimPureIO _ arg) = "#pureIO " ++ prettifyExprAsArg arg
prettifyExpr (PrimApplyIO _ func io) = "#applyIO " ++ prettifyExprAsArg func ++ " " ++ prettifyExprAsArg io
prettifyExpr (PrimBindIO _ io func) = "#bindIO " ++ prettifyExprAsArg io ++ " " ++ prettifyExprAsArg func
prettifyExpr (PrimIntEq _ left right) = "#intEq " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimStringEq _ left right) = "#stringEq " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimStringConcat _ left right) = "#stringConcat " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimIfThenElse _ cond then' else') = 
  "#ifThenElse " ++ prettifyExprAsArg cond ++ "\n  " ++ prettifyExprAsArg then' ++ "\n  " ++ prettifyExprAsArg else'
prettifyExpr (PrimIntSub _ left right) = "#intSub " ++ prettifyExprAsArg left ++ " " ++ prettifyExprAsArg right
prettifyExpr (PrimExit _ arg) = "#exit " ++ prettifyExprAsArg arg
-- Curried primitives
prettifyExpr (PrimFmapIOValue _) = "#fmapIO"
prettifyExpr (PrimPureIOValue _) = "#pureIO"
prettifyExpr (PrimApplyIOValue _) = "#applyIO"
prettifyExpr (PrimBindIOValue _) = "#bindIO"
prettifyExpr (PrimIntEqValue _) = "#intEq"
prettifyExpr (PrimStringEqValue _) = "#stringEq"
prettifyExpr (PrimStringConcatValue _) = "#stringConcat"
prettifyExpr (PrimIfThenElseValue _) = "#ifThenElse"
prettifyExpr (PrimIntSubValue _) = "#intSub"
prettifyExpr (PrimExitValue _) = "#exit"
prettifyExpr (PrimPrintValue _) = "#print"
prettifyExpr expr = "-- unsupported expression"  -- Fallback for any unhandled expressions

-- Helper function to determine if an expression needs parentheses when used as an argument
needsParensAsArg :: Expr PBinding -> Bool
needsParensAsArg (Lam _ _ _ _) = True  -- Lambda expressions always need parens
needsParensAsArg _ = False

-- Expression precedence levels (higher number = higher precedence)
exprPrecedence :: Expr PBinding -> Int
exprPrecedence (Lam _ _ _ _) = 0      -- Lowest precedence
exprPrecedence (PrimIfThenElse _ _ _ _) = 1  -- Conditionals are low precedence
exprPrecedence (PrimBindIO _ _ _) = 2    -- Monadic bind
exprPrecedence (PrimIntEq _ _ _) = 4     -- Comparison operators  
exprPrecedence (PrimStringEq _ _ _) = 4  -- Comparison operators
exprPrecedence (PrimIntSub _ _ _) = 6    -- Arithmetic operators
exprPrecedence (PrimStringConcat _ _ _) = 6  -- String concatenation
exprPrecedence (PrimFmapIO _ _ _) = 7    -- Map operations
exprPrecedence (PrimApplyIO _ _ _) = 7   -- Apply operations
exprPrecedence (App _ _ _) = 10       -- Function application (high precedence)
exprPrecedence _ = 11  -- Atomic expressions (variables, literals, etc.) have highest precedence

-- Determine if an expression needs parentheses based on context
needsParensInContext :: Int -> Expr PBinding -> Bool
needsParensInContext contextPrecedence expr = exprPrecedence expr < contextPrecedence

-- Check if this is a problematic nested stringConcat pattern
isProblematiStringConcat :: Expr PBinding -> Bool
isProblematiStringConcat (App _ func _) = 
  case func of
    App _ (PrimStringConcatValue _) _ -> True
    _ -> False
isProblematiStringConcat _ = False

-- Helper function to add parentheses around complex expressions
prettifyExprWithParens :: Expr PBinding -> String
prettifyExprWithParens expr = 
  if needsParensAsArg expr
  then "(" ++ prettifyExpr expr ++ ")"
  else prettifyExpr expr

-- Helper function for adding parentheses in function argument context  
prettifyExprAsArg :: Expr PBinding -> String
prettifyExprAsArg expr = 
  case expr of
    -- Function applications need parentheses when used as arguments to other functions
    App _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    -- Lambdas need parentheses  
    Lam _ _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    -- Conditionals need parentheses
    PrimIfThenElse _ _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    -- Some binary operations may need parentheses depending on context
    PrimIntSub _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    PrimBindIO _ _ _ -> "(" ++ prettifyExpr expr ++ ")"
    -- Atomic expressions don't need parentheses
    _ -> prettifyExpr expr

-- Smart application formatting with proper line breaks
prettifyApp :: Expr PBinding -> Expr PBinding -> String
prettifyApp func arg = 
  -- Don't flatten applications when the argument is complex
  -- This preserves the original parenthesized structure
  prettifyExpr func ++ " " ++ prettifyExprWithParens arg

-- Recursively find all .funk files in a directory
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
-- Fails if an explicitly specified file doesn't exist
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
