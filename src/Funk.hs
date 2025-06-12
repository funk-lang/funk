module Funk where

import Funk.Parser
import Funk.Token

run :: String -> IO ()
run s = case tokenize s of
  Left err -> putStrLn $ "Error: " ++ show err
  Right tokens -> case parseTerm tokens of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> putStrLn $ "Parsed term: " ++ show t
