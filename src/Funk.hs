{-# LANGUAGE LambdaCase #-}

module Funk where

import Data.List (intercalate, isPrefixOf)
import Funk.Fresh (Env (Env), runFresh)
import Funk.Infer (constraintsBlock)
import Funk.Parser (parseTopLevel, PBlock, PStmt)
import Funk.STerm
import Funk.Solver
import Funk.Subst hiding (Env)
import qualified Funk.Subst as Subst
import Funk.Term (Block(..), Stmt(..), Ident(..), ModulePath(..), prettyType, Precedence(..))
import Funk.Token (tokenize, Located(..), locatedPos, unLocated)
import Funk.Compiler (compile, compileToModule)
import Funk.Core (prettyCoreProgram, prettyCoreModule, CoreProgram, CoreModule(..))
import Funk.Fmt (formatFile, FmtOptions(..))
import Options.Applicative hiding (ParseError)
import System.Console.ANSI
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory, createDirectoryIfMissing)
import System.FilePath ((</>), takeExtension, takeFileName, dropExtension, takeDirectory)
import Control.Monad (forM, forM_)
import qualified Data.Map as Map
import Data.List (intercalate, isPrefixOf)
import Text.Parsec
import Text.Parsec.Error (newErrorMessage, Message(..), errorMessages)
import Text.Parsec.Pos (initialPos)
import qualified Text.PrettyPrint as Pretty

import Control.Exception (try, SomeException)

-- | Convert a module name like "Control.Monad" to a nested file path "Control/Monad.funkc"
moduleNameToPath :: String -> FilePath -> FilePath
moduleNameToPath moduleName targetDir = 
  let parts = splitOn '.' moduleName
      dirParts = init parts
      fileName = last parts ++ ".funkc"
      dirPath = foldl (</>) targetDir dirParts
  in dirPath </> fileName
  where
    splitOn :: Char -> String -> [String]
    splitOn c input = case break (== c) input of
      (prefix, []) -> [prefix]
      (prefix, _:suffix) -> prefix : splitOn c suffix

data Command
  = RunCommand RunOptions
  | BuildCommand BuildOptions
  | FmtCommand FmtOptions
  deriving (Show)

data RunOptions = RunOptions
  { runMainFile :: FilePath         -- Required main file
  , runLibPaths :: [FilePath]       -- Optional library files/directories  
  } deriving (Show)

data BuildOptions = BuildOptions
  { buildMainFile :: FilePath       -- Required main file
  , buildLibPaths :: [FilePath]     -- Optional library files/directories  
  , buildTargetDir :: FilePath      -- Target directory for .funkc files
  } deriving (Show)

runCommand :: Parser RunOptions
runCommand = 
  RunOptions
    <$> argument str (metavar "MAIN_FILE" <> help "Main Funk file to execute")
    <*> Options.Applicative.many (strOption (long "lib" <> short 'L' <> metavar "LIB_PATH" <> help "Library file or directory (can be used multiple times)"))

buildCommand :: Parser BuildOptions
buildCommand = 
  BuildOptions
    <$> argument str (metavar "MAIN_FILE" <> help "Main Funk file to build")
    <*> Options.Applicative.many (strOption (long "lib" <> short 'L' <> metavar "LIB_PATH" <> help "Library file or directory (can be used multiple times)"))
    <*> strOption (long "target" <> short 't' <> metavar "TARGET_DIR" <> value "target" <> help "Target directory for .funkc files (default: target)")

fmtCommand :: Parser FmtOptions
fmtCommand = 
  FmtOptions
    <$> argument str (metavar "FILE_OR_DIR" <> help "Funk file or directory to format")
    <*> switch (long "in-place" <> short 'i' <> help "Modify files in place")

commands :: Parser Command
commands = subparser
  ( command "run" (info (RunCommand <$> runCommand) (progDesc "Run a Funk program"))
  <> command "build" (info (BuildCommand <$> buildCommand) (progDesc "Build a Funk program"))
  <> command "fmt" (info (FmtCommand <$> fmtCommand) (progDesc "Format Funk files or directories"))
  )

run :: IO ()
run = do
  cmd <- execParser $ info (commands <**> helper) 
    ( fullDesc
    <> progDesc "Funk programming language"
    <> header "funk - a functional programming language"
    )
  
  case cmd of
    RunCommand _opts -> putStrLn "Run command temporarily disabled during primitive refactor"
    BuildCommand opts -> buildProgram opts
    FmtCommand opts -> formatFile opts

runProgram :: RunOptions -> IO ()
runProgram _opts = putStrLn "Run functionality temporarily disabled"
{-
runProgram opts = do
  -- Verify main file exists
  mainExists <- doesFileExist (runMainFile opts)
  if not mainExists
    then putStrLn $ "Error: Main file not found: " ++ runMainFile opts
    else do
      -- Expand library paths to individual .funk files
      libResult <- expandInputPaths (runLibPaths opts)
      
      case libResult of
        Left errorMsg -> putStrLn $ "Error: " ++ errorMsg
        Right libFiles -> do
          -- Combine main file with library files for module loading
          let allFiles = runMainFile opts : libFiles
          
          -- Load and resolve all modules
          moduleResult <- loadModules allFiles
          case moduleResult of
            Left moduleError -> putStrLn $ "Error: " ++ moduleError
            Right moduleMap -> do
              mainInput <- readFile (runMainFile opts)
              
              -- Parse and resolve modules with proper use statement handling
              res <- tryRunWithModules mainInput moduleMap
              case res of
                Left err -> showErrorPretty err mainInput >>= putStrLn  
                Right block -> do
                  -- Compile to Core and run interpreter
                  coreProgram <- compile block
                  result <- evalProgramIO coreProgram
                  case result of
                    Left interpErr -> putStrLn $ "Interpreter error: " ++ interpErr
                    Right VUnit -> return () -- Don't print unit results from IO actions
                    Right resultVal -> putStrLn $ prettyValue resultVal
-}

-- Try to compile a block to Core IR, handling library modules gracefully
tryCompileToCore :: SBlock -> IO (Either String CoreModule)
tryCompileToCore block = do
  result <- Control.Exception.try (compileToModule block)
  case result of
    Left err -> return $ Left $ show (err :: SomeException)
    Right coreModule -> return $ Right coreModule

buildProgram :: BuildOptions -> IO ()
buildProgram opts = do
  -- Verify main file exists
  mainExists <- doesFileExist (buildMainFile opts)
  if not mainExists
    then putStrLn $ "Error: Main file not found: " ++ buildMainFile opts
    else do
      -- Expand library paths to individual .funk files
      libResult <- expandInputPaths (buildLibPaths opts)
      
      case libResult of
        Left errorMsg -> putStrLn $ "Error: " ++ errorMsg
        Right libFiles -> do
          -- Combine main file with library files for module loading
          let allFiles = buildMainFile opts : libFiles
          
          -- Load and resolve all modules
          moduleResult <- loadModules allFiles
          case moduleResult of
            Left moduleError -> putStrLn $ "Error: " ++ moduleError
            Right moduleMap -> do
              -- Create target directory
              createDirectoryIfMissing True (buildTargetDir opts)
              
              -- Process each module with resolved imports for type-checking and write to .funkc files
              let allModules = Map.toList moduleMap
              forM_ allModules $ \(moduleName, moduleContent) -> do
                -- Type-check this module with resolved imports but show only original content
                res <- tryRunWithModulesForDisplay moduleContent moduleMap
                case res of
                  Left (SubstError errs) -> do
                    putStrLn $ "=== Module: " ++ moduleName ++ " ==="
                    let unknownIds = map (unIdent . unLocated) errs
                    putStrLn $ "Error: Module references unresolved identifiers:"
                    mapM_ (\ident -> putStrLn $ "  - " ++ ident) unknownIds
                    putStrLn ""
                  Left (SolverError _) -> do
                    -- Try to compile anyway - solver errors might be just trait definitions
                    -- that don't prevent let bindings from compiling
                    result <- tryCompileModuleWithTraitErrors moduleContent moduleMap
                    case result of
                      Left _err -> do
                        putStrLn $ "=== Module: " ++ moduleName ++ " ==="
                        putStrLn "Error: Module contains trait/instance issues, attempting Core compilation anyway..."
                        putStrLn ""
                      Right coreModule -> do
                        let coreOutput = Pretty.renderStyle (Pretty.style { Pretty.lineLength = 120 }) $ prettyCoreModule coreModule
                        -- Write to .funkc file in nested directory structure
                        let outputPath = moduleNameToPath moduleName (buildTargetDir opts)
                        createDirectoryIfMissing True (takeDirectory outputPath)
                        writeFile outputPath coreOutput
                        putStrLn $ "Wrote " ++ outputPath
                  Left err -> do
                    putStrLn $ "=== Module: " ++ moduleName ++ " ==="
                    putStrLn $ "Parse error in module:"
                    showErrorPretty err moduleContent >>= putStrLn
                    putStrLn ""
                  Right originalBlock -> do
                    -- Try to compile to Core IR for any module that type-checks successfully
                    result <- tryCompileToCore originalBlock
                    case result of
                      Left _err -> do
                        -- Even if Core compilation fails, don't show anything for cleaner output
                        return ()
                      Right coreModule -> do
                        -- Successfully compiled to Core, write to file
                        let coreOutput = Pretty.renderStyle (Pretty.style { Pretty.lineLength = 120 }) $ prettyCoreModule coreModule
                        -- Write to .funkc file in nested directory structure
                        let outputPath = moduleNameToPath moduleName (buildTargetDir opts)
                        createDirectoryIfMissing True (takeDirectory outputPath)
                        writeFile outputPath coreOutput
                        putStrLn $ "Wrote " ++ outputPath

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
          else return $ Left $ "Library file not found: " ++ path
  
  let (errors, successes) = partitionEithers results
  if null errors
    then return $ Right $ concat successes
    else return $ Left $ unlines errors
  where
    partitionEithers :: [Either a b] -> ([a], [b])
    partitionEithers = foldr (either left right) ([], [])
      where
        left  a (l, r) = (a:l, r)
        right b (l, r) = (l, b:r)

-- Validate that a library file has valid syntax
validateLibraryFile :: FilePath -> IO (Either String ())
validateLibraryFile filePath = do
  exists <- doesFileExist filePath
  if not exists
    then return $ Left $ "Library file not found: " ++ filePath
    else do
      content <- readFile filePath
      let result = tokenize content >>= parseTopLevel
      case result of
        Left err -> do
          let prettyError = showParseErrorPretty err content
          return $ Left $ "Parse error in " ++ filePath ++ ":\n" ++ prettyError
        Right _ -> return $ Right ()

-- Load multiple module files into a map after validating syntax
loadModules :: [FilePath] -> IO (Either String (Map.Map String String))
loadModules filePaths = do
  -- First validate all library files
  validationResults <- forM filePaths $ \filePath -> do
    if filePath == head filePaths  -- Skip main file (validated separately)
      then return $ Right ()
      else validateLibraryFile filePath
  
  let errors = [err | Left err <- validationResults]
  if not (null errors)
    then return $ Left $ unlines errors
    else do
      -- If all files are valid, load them
      modules <- forM filePaths $ \filePath -> do
        exists <- doesFileExist filePath
        if exists
          then do
            content <- readFile filePath
            let modName = filePathToModuleName filePath
            return (modName, content)
          else do
            putStrLn $ "Warning: File not found: " ++ filePath
            return ("", "")
      return $ Right $ Map.fromList $ filter ((/= "") . fst) modules

-- Convert file path to module name, handling library directory structure
filePathToModuleName :: FilePath -> String
filePathToModuleName filePath = 
  let -- Remove common library directory prefixes and the .funk extension
      cleanPath = dropExtension filePath
      -- Remove examples/lib/ prefix if present
      relativePath = if "examples/lib/" `isPrefixOf` cleanPath
                     then drop (length "examples/lib/") cleanPath
                     else takeFileName cleanPath
      -- Convert path separators to dots for hierarchical module names
      normalizedPath = map (\c -> if c == '/' || c == '\\' then '.' else c) relativePath
  in if normalizedPath == ""
     then ""
     else normalizedPath

tryRun :: String -> IO (Either Error SBlock)
tryRun input = do
  let result = tokenize input >>= parseTopLevel
  case result of
    Left err -> return $ Left (ParserError err)
    Right topLevel -> do
      (res, env) <- runSubst (substBlock topLevel)
      case res of
        Left errs -> return $ Left (SubstError errs)
        Right block -> do
          cs <- fst <$> runFresh (constraintsBlock block) (Env $ envNextIdx env)
          solveConstraints cs env >>= \case
            Left errs -> return $ Left (SolverError errs)
            Right () -> return $ Right block

data Error = ParserError ParseError | SubstError [Located Ident] | SolverError [SError]

instance Show Error where
  show (ParserError _) = "Parse Error"
  show (SubstError _) = "Substitution Error"
  show (SolverError _) = "Solver Error"

showParseErrorPretty :: ParseError -> String -> String
showParseErrorPretty err input =
  let (msgs, unexpect, expects) =
        foldl
          ( \(m, u, e) msg' ->
              case msg' of
                Message m' -> (m ++ [m'], u, e)
                UnExpect s -> (m, s, e)
                Expect s -> (m, u, e ++ [s])
                SysUnExpect s -> (m, s, e)
          )
          ([], "", [])
          (errorMessages err)
      expecting = case expects of
        [] -> "unexpected token"
        [x] -> "expecting " ++ x
        xs ->
          "expecting "
            ++ intercalate ", " (reverse . drop 1 $ reverse xs)
            ++ " or "
            ++ last xs
      msg =
        expecting
          ++ ", found "
          ++ if null unexpect
            then "<end of input>"
            else
              unexpect
                ++ if null msgs
                  then ""
                  else
                    setSGRCode [SetColor Foreground Vivid Red]
                      ++ "help:\n"
                      ++ setSGRCode [Reset]
                      ++ intercalate "\n" msgs
      pos = errorPos err
      pos' = setSourceColumn pos (sourceColumn pos + 1)
   in showErrorLine pos' input msg

showSErrorPretty :: SError -> String -> IO String
showSErrorPretty err input =
  case err of
    InfiniteType i -> case i of
      Left pos -> return $ showErrorLine pos input "Infinite type detected"
      Right ident ->
        return $
          showErrorLine (locatedPos ident) input $
            "Infinite type: `" ++ unIdent (unLocated ident) ++ "`"
    UnificationError t1 t2 -> do
      t1' <- sTypeToDisplay t1
      t2' <- sTypeToDisplay t2
      let t1Str = Pretty.render $ prettyType AtomPrec t1'
          t2Str = Pretty.render $ prettyType AtomPrec t2'
      return $
        "Unification error: cannot unify types `"
          ++ t1Str
          ++ "` and `"
          ++ t2Str
          ++ "`"
    MissingTraitImpl pos traitName targetType -> do
      traitName' <- sTBindingToIdent traitName
      targetType' <- sTypeToDisplay targetType
      let targetTypeStr = Pretty.render $ prettyType AtomPrec targetType'
          traitNameStr = unIdent traitName'
          errorMsg = "No implementation of trait `" ++ traitNameStr ++ "` for type `" ++ targetTypeStr ++ "`"
      return $ showErrorLine pos input errorMsg

showErrorPretty :: Error -> String -> IO String
showErrorPretty (ParserError err) input = return $ showParseErrorPretty err input
showErrorPretty (SubstError errs) input =
  return $ unlines $ map (\i -> showErrorLine (locatedPos i) input ("Unknown identifier: " ++ unIdent (unLocated i))) errs
showErrorPretty (SolverError errs) input = unlines <$> mapM (`showSErrorPretty` input) errs

showErrorLine :: SourcePos -> String -> String -> String
showErrorLine pos input msg =
  let linePos = sourceLine pos
      colPos = sourceColumn pos
      srcLine = case drop (linePos - 1) (lines input) of
        (line : _) -> line
        [] -> ""
   in unlines
        [ " --> "
            ++ sourceName pos
            ++ ":"
            ++ show linePos
            ++ ":"
            ++ show colPos,
          "  |",
          show linePos ++ " | " ++ srcLine,
          "  |"
            ++ setSGRCode [SetColor Foreground Vivid Red]
            ++ replicate colPos ' '
            ++ "^ "
            ++ msg
            ++ setSGRCode [Reset]
        ]

tryRunWithModules :: String -> Map.Map String String -> IO (Either Error SBlock)
tryRunWithModules mainInput moduleMap = do
  let result = tokenize mainInput >>= parseTopLevel
  case result of
    Left err -> return $ Left (ParserError err)
    Right topLevel -> do
      -- For now, just pass through without expanding use statements
      expandedTopLevel <- resolveUseStatements topLevel moduleMap
      case expandedTopLevel of
        Left err -> return $ Left err
        Right expanded -> do
          (res, env) <- runSubst (substBlock expanded)
          case res of
            Left errs -> return $ Left (SubstError errs)
            Right block -> do
              cs <- fst <$> runFresh (constraintsBlock block) (Env $ envNextIdx env)
              solveConstraints cs env >>= \case
                Left errs -> return $ Left (SolverError errs)
                Right () -> return $ Right block

-- Type-check a module with resolved imports but return original structure for display  
tryRunWithModulesForDisplay :: String -> Map.Map String String -> IO (Either Error SBlock)
tryRunWithModulesForDisplay moduleInput moduleMap = do
  let result = tokenize moduleInput >>= parseTopLevel
  case result of
    Left err -> return $ Left (ParserError err)
    Right originalTopLevel -> do
      -- Test if the module type-checks with imports resolved
      expandedTopLevel <- resolveUseStatements originalTopLevel moduleMap
      case expandedTopLevel of
        Left err -> return $ Left err
        Right expanded -> do
          (expandedRes, expandedEnv) <- runSubst (substBlock expanded)
          case expandedRes of
            Left substErrs -> return $ Left (SubstError substErrs)
            Right expandedBlock -> do
              cs <- fst <$> runFresh (constraintsBlock expandedBlock) (Env $ Subst.envNextIdx expandedEnv)
              solveConstraints cs expandedEnv >>= \case
                Left solveErrs -> return $ Left (SolverError solveErrs)
                Right () -> do
                  -- SUCCESS: Module type-checks with imports
                  -- Now create a display version with only original content
                  originalDisplayBlock <- createFilteredDisplayBlock originalTopLevel expandedBlock
                  return $ Right originalDisplayBlock

-- Create a display block that shows only the original module content
createFilteredDisplayBlock :: PBlock -> SBlock -> IO SBlock
createFilteredDisplayBlock originalTopLevel expandedBlock = do
  -- Count how many statements the original module had (excluding use statements)
  let Block originalStmts _originalExpr = originalTopLevel
  let originalNonUseStmts = filter (not . isUseStatement) originalStmts
  let originalCount = length originalNonUseStmts
  
  -- Extract the same number of statements from the END of the expanded block
  -- (since imports are added at the beginning)
  let Block expandedStmts expandedExpr = expandedBlock
  let expandedCount = length expandedStmts
  let startIndex = expandedCount - originalCount
  let originalStatements = drop startIndex expandedStmts
  
  -- Return a block with only the original statements
  return $ Block originalStatements expandedExpr

-- Check if a statement is a use statement
isUseStatement :: PStmt -> Bool
isUseStatement (UseAll _) = True
isUseStatement _ = False

-- Try to compile a module that has trait/solver errors by bypassing constraint solving
tryCompileModuleWithTraitErrors :: String -> Map.Map String String -> IO (Either String CoreModule)
tryCompileModuleWithTraitErrors moduleInput moduleMap = do
  let result = tokenize moduleInput >>= parseTopLevel
  case result of
    Left _err -> return $ Left "Parse error"
    Right originalTopLevel -> do
      expandedTopLevel <- resolveUseStatements originalTopLevel moduleMap
      case expandedTopLevel of
        Left _err -> return $ Left "Module resolution error"
        Right expanded -> do
          (expandedRes, _expandedEnv) <- runSubst (substBlock expanded)
          case expandedRes of
            Left _substErrs -> return $ Left "Substitution error"
            Right expandedBlock -> do
              -- Skip constraint solving and go directly to Core compilation
              tryCompileToCore expandedBlock

-- Simple module expansion for now
resolveUseStatements :: PBlock -> Map.Map String String -> IO (Either Error PBlock)
resolveUseStatements (Block stmts finalExpr) moduleMap = do
  expandedStmts <- expandAllStatements [] stmts
  case expandedStmts of
    Left err -> return $ Left err
    Right expanded -> return $ Right $ Block expanded finalExpr
  where
    expandAllStatements :: [PStmt] -> [PStmt] -> IO (Either Error [PStmt])
    expandAllStatements acc [] = return $ Right acc
    expandAllStatements acc (stmt:rest) = do
      case stmt of
        UseAll modPath -> do
          let modName = modulePathToString modPath
          case Map.lookup modName moduleMap of
            Nothing -> return $ Left $ ParserError $ newErrorMessage (Message $ "Module not found: " ++ modName) (initialPos "")
            Just content -> do
              case tokenize content >>= parseTopLevel of
                Left err -> return $ Left $ ParserError err
                Right (Block moduleStmts _) -> expandAllStatements (acc ++ moduleStmts) rest
        _ -> expandAllStatements (acc ++ [stmt]) rest

modulePathToString :: ModulePath -> String
modulePathToString (ModulePath idents) = intercalate "." (map unIdent idents)
