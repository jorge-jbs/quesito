module Main where

import System.Environment (getArgs)
import Data.Maybe (fromJust)

import Quesito.AnnTerm
import Quesito.Compile.CodeGen
import Quesito.NameProv (runNameProv)
import Quesito.Parse

main :: IO ()
main = do
  args <- getArgs
  putStrLn
    $ toProgram
    $ runNameProv
    $ compile
    $ fromJust
    $ annotate
    $ either (error . show) id
    $ parse (args !! 0)
