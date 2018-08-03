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
checkEvalProgram ((name, def) : defs) evaledDefs = do
  def' <- checkEvalDef evaledDefs def
  checkEvalProgram defs ((name, def') : evaledDefs)

checkEvalDef :: [(Name, Def Value Value)] -> Def CheckTerm InfTerm -> Result (Def Value Value)
checkEvalDef evaledDefs (DExpr expr ty) = do
  _ <- typeInf evaledDefs [] ty
  let ty' = evalInf evaledDefs [] ty
  typeCheck evaledDefs [] expr ty'
  let expr' = evalCheck evaledDefs [] expr
  return (DExpr expr' ty')
checkEvalDef evaledDefs (DDataType ty) = do
  tyTy <- typeInf evaledDefs [] ty
  case tyTy of
    VType _ ->
      return (DDataType (evalInf evaledDefs [] ty))
    _ ->
      Left "Type constructor is not of type Type"
checkEvalDef evaledDefs (DDataCons ty) = do
  tyTy <- typeInf evaledDefs [] ty
  case tyTy of
    VType _ ->
      return (DDataCons (evalInf evaledDefs [] ty))
    _ ->
      Left "Type constructor is not of type Type"
