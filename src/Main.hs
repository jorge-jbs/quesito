module Main where

import Control.Monad (unless, forM_)

import Quesito.TT
import Quesito.Parse

main :: IO ()
main = do
  input <- getContents
  let
    definitions
      = either (error . show) id
      $ parse input
  case checkProgram definitions [] of
    Right () ->
      putStrLn "Type check ok"
    Left err ->
      putStrLn ("Type checking failed: " ++ err)

checkProgram :: [(Name, CheckTerm, CheckTerm)] -> [(Name, Value)] -> Result ()
checkProgram [] _ = Right ()
checkProgram ((name, ty, expr) : defs) scope = do
  let ty' = evalCheck [] ty
  typeCheck scope expr ty'
  checkProgram defs ((name, ty') : scope)
