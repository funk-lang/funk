{-# LANGUAGE LambdaCase #-}

module Funk where

import Data.List (intercalate, isPrefixOf)
import Funk.Fresh (Env (Env), runFresh)
import Funk.Infer (constraintsBlock)
import Funk.Parser (parseTopLevel, PBlock, PStmt)
import Funk.STerm
import Funk.Solver
import Funk.Subst hiding (Env)
import Funk.Term (Block(..), Stmt(..), Ident(..), ModulePath(..), showFileWithTypes, prettyType, Precedence(..))
import Funk.Token (tokenize, Located, locatedPos, unLocated)
import Funk.Compiler (compile)
import Funk.Interpreter (evalProgramIO, prettyValue, Value(..))
import Funk.Fmt (formatFile, FmtOptions(..))
import Options.Applicative hiding (ParseError)
import System.Console.ANSI
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension, takeFileName, dropExtension)
import Control.Monad (forM)
import qualified Data.Map as Map
import Text.Parsec
import Text.Parsec.Error (newErrorMessage, Message(..), errorMessages)
import Text.Parsec.Pos (initialPos)
import qualified Text.PrettyPrint as Pretty

data Command
  = RunCommand RunOptions
  | FmtCommand FmtOptions
  deriving (Show)

data RunOptions = RunOptions
  { runMainFile :: FilePath         -- Required main file
  , runLibPaths :: [FilePath]       -- Optional library files/directories  
  , runInterpret :: Bool
  } deriving (Show)

runCommand :: Parser RunOptions
runCommand = 
  RunOptions
    <$> argument str (metavar "MAIN_FILE" <> help "Main Funk file to execute")
    <*> Options.Applicative.many (strOption (long "lib" <> short 'L' <> metavar "LIB_PATH" <> help "Library file or directory (can be used multiple times)"))
    <*> switch (long "interpret" <> short 'i' <> help "Run the interpreter instead of pretty-printing")

fmtCommand :: Parser FmtOptions
fmtCommand = 
  FmtOptions
    <$> argument str (metavar "FILE_OR_DIR" <> help "Funk file or directory to format")
    <*> switch (long "in-place" <> short 'i' <> help "Modify files in place")

commands :: Parser Command
commands = subparser
  ( command "run" (info (RunCommand <$> runCommand) (progDesc "Run a Funk program"))
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
    RunCommand opts -> runProgram opts
    FmtCommand opts -> formatFile opts

runProgram :: RunOptions -> IO ()
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
                  if runInterpret opts
                    then do
                      -- Compile to Core and run interpreter
                      coreProgram <- compile block
                      result <- evalProgramIO coreProgram
                      case result of
                        Left interpErr -> putStrLn $ "Interpreter error: " ++ interpErr
                        Right VUnit -> return () -- Don't print unit results from IO actions
                        Right resultVal -> putStrLn $ prettyValue resultVal
                    else do
                                            -- Output the pretty-printed resolved AST with proper type resolution
                      resolvedBlock <- sBlockToDisplayWithTypes block
                      putStrLn $ showFileWithTypes [] resolvedBlock

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
