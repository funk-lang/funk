module Main (main) where

-- Import all test modules

import qualified Funk.ParserSpec
import qualified Funk.SimpleSpec
import qualified Funk.TokenSpec
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "Funk Language Tests" $ do
    Funk.TokenSpec.spec
    Funk.ParserSpec.spec
    Funk.SimpleSpec.spec
