module Main where

import Data.Maybe (fromJust)

import Quesito.IL
import Quesito.Eval
import Quesito.Parse

main :: IO ()
main = do
  input <- getContents
  putStrLn
    $ show
    $ eval
    $ maybe (error "Could not desugar") id
    $ desugar
    $ either (error . show) id
    $ parse input
