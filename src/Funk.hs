module Funk where

import Data.List
import Funk.Parser (parseTerm)
import Funk.Term
import Funk.Token
import Funk.TypeChecker
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
    Right term -> case typeOf term of
      Left err -> do
        let (pos, msg) = case err of
              NotForall t -> (typePos t, "expected forall")
              NotAFunction t -> (typePos t, "expected function type")
              Mismatch t1 t2 ->
                ( typePos t1,
                  "expected type: "
                    ++ showTypePretty t1
                    ++ ", but found: "
                    ++ showTypePretty t2
                )
              UnboundTermVar v ->
                ( locatedPos v,
                  "unbound variable `"
                    ++ show (unIdent $ unLocated v)
                    ++ "`"
                )
        putStrLn $ showErrorLine pos input msg
      Right ty -> putStrLn $ showTypePretty ty

typePos :: Type -> SourcePos
typePos (TVar (Located pos _)) = pos
typePos (TArrow t1 _) = typePos t1
typePos (TForall (Located pos _) _) = pos

showTypePretty :: Type -> String
showTypePretty (TVar (Located _ a)) = unIdent a
showTypePretty (TArrow t1 t2) =
  showTypePretty t1 ++ " -> " ++ showTypePretty t2
showTypePretty (TForall (Located _ a) t) =
  "\\/ " ++ unIdent a ++ ". " ++ showTypePretty t

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
