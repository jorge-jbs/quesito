module Main where

import Quesito.Eval
import Quesito.Parse

main :: IO ()
main = do
  input <- getContents
  putStrLn
    $ show
    $ eval
    $ either (error . show) id
    $ parse input
