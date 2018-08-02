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
  case head <$> checkEvalProgram definitions [] of
    Right (_, DExpr e _) ->
      putStrLn $ show $ quote e
    Left err ->
      putStrLn ("Type checking failed: " ++ err)

checkEvalProgram
  :: [(Name, Def CheckTerm InfTerm)]
  -> [(Name, Def Value Value)]
  -> Result [(Name, Def Value Value)]
checkEvalProgram [] definitions = Right definitions
checkEvalProgram ((name, DExpr expr ty) : defs) definitions = do
  _ <- typeInf definitions [] ty
  let ty' = evalInf definitions [] ty
  typeCheck definitions [] expr ty'
  let expr' = evalCheck definitions [] expr
  checkEvalProgram defs ((name, DExpr expr' ty') : definitions)
