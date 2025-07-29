{-# LANGUAGE LambdaCase #-}

module Funk where

import Data.List
import Funk.Fresh (Env (Env))
import Funk.Infer (infer)
import Funk.Parser (parseTopLevel)
import Funk.STerm
import Funk.Solver
import Funk.Subst hiding (Env)
import Funk.Term
import Funk.Token
import Options.Applicative hiding (ParseError)
import System.Console.ANSI
import Text.Parsec
import Text.Parsec.Error
import qualified Text.PrettyPrint as Pretty

newtype Options = Options {optionsFilePath :: FilePath}

options :: Parser Options
options =
  Options <$> argument str (metavar "FILE" <> help "Path to the input file")

run :: IO ()
run = do
  opts <- execParser $ info (options <**> helper) fullDesc
  input <- readFile (optionsFilePath opts)
  res <- tryRun input
  case res of
    Left err -> showErrorPretty err input >>= putStr
    Right block -> do
      block' <- sBlockToDisplay block
      putStrLn $ showFile block'

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
          cs <- infer block (Env $ envNextIdx env)
          solveConstraints cs env >>= \case
            Left errs -> return $ Left (SolverError errs)
            Right () -> return $ Right block

data Error
  = ParserError ParseError
  | SubstError [Located Ident]
  | SolverError [SError]

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
      linePosStr = show linePos
      indent = replicate (length linePosStr) ' '
   in unlines
        [ indent
            ++ "--> "
            ++ sourceName pos
            ++ ":"
            ++ show linePos
            ++ ":"
            ++ show colPos,
          indent ++ " |",
          show linePos ++ " | " ++ srcLine,
          indent
            ++ " |"
            ++ setSGRCode [SetColor Foreground Vivid Red]
            ++ replicate colPos ' '
            ++ "^ "
            ++ msg
            ++ setSGRCode [Reset]
        ]
