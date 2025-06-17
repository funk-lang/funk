module Funk where

import Data.List
import Funk.Parser (parseTerm)
import Funk.Solver
import Funk.Term
import Funk.Token
import Options.Applicative
import System.Console.ANSI
import Text.Parsec
import Text.Parsec.Error

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
  let result = tokenize input >>= parseTerm
  case result of
    Left err -> do
      let (msgs, unexpect, expects) =
            foldl
              ( \(m, u, e) msg ->
                  case msg of
                    Message m' -> (m ++ [m'], u, e)
                    UnExpect s -> (m, s, e)
                    Expect s -> (m, u, e ++ [s])
                    SysUnExpect s -> (m, s, e)
              )
              ([], "", [])
              (errorMessages err)
      let expecting = case expects of
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
      let pos = errorPos err
          pos' = setSourceColumn pos (sourceColumn pos + 1)
      putStrLn $ showErrorLine pos' input msg
    Right term -> do
      res <- solvePTerm term
      case res of
        Left errs -> do
          let errMsgs =
                map
                  ( \err ->
                      showErrorLine
                        (locatedPos err)
                        ("Unbound identifier: " ++ unIdent (unLocated err))
                        input
                  )
                  errs
          putStrLn $ unlines errMsgs
        Right st -> do
          s <- showSTerm st
          putStrLn s

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
