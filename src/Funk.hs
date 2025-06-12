module Funk where

import Funk.Token

run :: String -> IO ()
run s = print $ tokenize s
