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
checkEvalProgram [] evaledDefs = Right evaledDefs
checkEvalProgram ((name, DExpr expr ty) : defs) evaledDefs = do
  _ <- typeInf evaledDefs [] ty
  let ty' = evalInf evaledDefs [] ty
  typeCheck evaledDefs [] expr ty'
  let expr' = evalCheck evaledDefs [] expr
  checkEvalProgram defs ((name, DExpr expr' ty') : evaledDefs)
