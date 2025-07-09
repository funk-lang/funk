module Funk where

import Data.List
import Funk.Parser (parseTerm)
import Funk.Solver
import Funk.Term
import Funk.Token
import Options.Applicative hiding (ParseError)
import System.Console.ANSI
import Text.Parsec
import Text.Parsec.Error
import Funk.STerm

newtype Options = Options
  { optionsFilePath :: FilePath
  }

options :: Parser Options
options =
  Options <$> argument str (metavar "FILE" <> help "Path to the input file")

run :: IO ()
run = do
  opts <- execParser $ info (options <**> helper) fullDesc
  input <- readFile (optionsFilePath opts)
  res <- tryRun input
  case res of
    Left err -> showErrorPretty err input >>= putStrLn
    Right st -> do
      stStr <- showSTerm st
      putStrLn stStr

tryRun :: String -> IO (Either Error STerm)
tryRun input = do
  let result = tokenize input >>= parseTerm
  case result of
    Left err -> return $ Left (ParserError err)
    Right term -> do
      res <- solvePTerm term
      case res of
        Left errs -> return $ Left (SolverError errs)
        Right st -> return $ Right st

data Error = ParserError ParseError | SolverError [SError]

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
            ++ intercalate ", " (reverse . tail $ reverse xs)
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
    MissingIdent i ->
      return $
        showErrorLine (locatedPos i) input $
          "Unknown identifier `" ++ unIdent (unLocated i) ++ "`"
    InfiniteType i -> case i of
      Left pos -> return $ showErrorLine pos input "Infinite type detected"
      Right ident ->
        return $
          showErrorLine (locatedPos ident) input $
            "Infinite type: `" ++ unIdent (unLocated ident) ++ "`"
    UnificationError t1 t2 -> do
      t1Str <- showSType t1
      t2Str <- showSType t2
      return $
        "Unification error: cannot unify types `"
          ++ t1Str
          ++ "` and `"
          ++ t2Str
          ++ "`"

showErrorPretty :: Error -> String -> IO String
showErrorPretty (ParserError err) input = return $ showParseErrorPretty err input
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
