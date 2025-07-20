{-|
Module      : Main
Description : FunkVM CLI interface
Copyright   : (c) 2025
License     : MIT

Command-line interface for the Funk Virtual Machine.
Provides options for loading library files, type checking, and program execution.
-}
module Main where

import Funk.Interpreter
import Funk.Core.Parser
import Options.Applicative
import System.Directory (doesFileExist)
import System.FilePath (takeExtension)

-- | Command line options
data Options = Options
  { optMainFile :: FilePath
  , optLibFiles :: [FilePath]
  , optTypeCheck :: Bool
  } deriving (Show)

-- | Parse command line options
options :: Parser Options
options = Options
  <$> argument str (metavar "MAIN_FILE" <> help "Main .funkc file to execute")
  <*> many (strOption (long "lib" <> short 'L' <> metavar "FILE" <> help "Library .funkc file to load"))
  <*> switch (long "typecheck-only" <> short 't' <> help "Only perform type checking, don't execute")

-- | Validate that a file exists and has .funkc extension
validateFunkcFile :: FilePath -> IO (Either String ())
validateFunkcFile filePath = do
  exists <- doesFileExist filePath
  if not exists
    then return $ Left $ "File does not exist: " ++ filePath
    else if takeExtension filePath /= ".funkc"
      then return $ Left $ "File is not a .funkc file: " ++ filePath
      else return $ Right ()

-- | Quick type checking of a .funkc file
quickTypeCheck :: FilePath -> IO (Either String ())
quickTypeCheck filePath = do
  content <- readFile filePath
  case parseFunkcFile content of
    Left parseErr -> return $ Left $ "Parse error: " ++ show parseErr
    Right _ -> return $ Right ()

-- | Main application logic
runApp :: Options -> IO ()
runApp opts = do
  -- Validate all input files
  let allFiles = optMainFile opts : optLibFiles opts
  validationResults <- mapM validateFunkcFile allFiles
  
  case sequence validationResults of
    Left err -> putStrLn $ "Error: " ++ err
    Right _ -> do
      if optTypeCheck opts
        then do
          -- Type check all files
          typeCheckResults <- mapM quickTypeCheck allFiles
          case sequence typeCheckResults of
            Left err -> putStrLn $ "Type check failed: " ++ err
            Right _ -> putStrLn "Type checking passed for all files."
        else do
          -- Quick type check first
          typeCheckResults <- mapM quickTypeCheck allFiles
          case sequence typeCheckResults of
            Left err -> putStrLn $ "Type check failed: " ++ err
            Right _ -> do
              -- Run the program silently
              runProgram (optMainFile opts) (optLibFiles opts)

main :: IO ()
main = do
  opts <- execParser $ info (options <**> helper)
    ( fullDesc
    <> progDesc "FunkVM - Virtual Machine for Funk programming language"
    <> header "funkvm - run compiled Funk programs (.funkc files)"
    )
  runApp opts
