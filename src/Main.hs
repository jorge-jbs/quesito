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
      putStrLn $ show $ quote $ evalProgram definitions []
    Left err ->
      putStrLn ("Type checking failed: " ++ err)

checkProgram :: [(Name, CheckTerm, CheckTerm)] -> [(Name, Value)] -> Result ()
checkProgram [] _ = Right ()
checkProgram ((name, ty, expr) : defs) scope = do
  let ty' = evalCheck [] ty
  typeCheck scope expr ty'
  checkProgram defs ((name, ty') : scope)

evalProgram :: [(Name, CheckTerm, CheckTerm)] -> [(Name, Value)] -> Value
evalProgram ((name, _, e) : defs) scope =
  let
    v = evalCheck scope e
  in
    case defs of
      [] -> v
      _ -> evalProgram defs ((name, v) : scope)
