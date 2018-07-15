module Main where

import Data.Maybe (fromJust)

import Quesito.AnnTerm
import Quesito.Compile.CodeGen
import Quesito.NameProv (runNameProv)
import Quesito.Parse

main :: IO ()
main = do
  input <- getContents
  putStr
    $ toProgram
    $ runNameProv
    $ compile
    $ fromJust
    $ annotate
    $ either (error . show) id
    $ parse input
