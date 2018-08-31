module Main where

import Control.Monad (unless, forM_)

import Quesito.TT
import Quesito.Parse

main :: IO ()
main = do
  input <- getContents
  let
    declarations
      = either (error . show) id
      $ parse input
  case head <$> checkEvalProgram declarations [] of
    Right (_, DMatchFunction [([], e)] _) ->
      putStrLn $ show $ quote (e [])
    Left err ->
      putStrLn ("Type checking failed: " ++ err)

checkEvalProgram
  :: [Decl]
  -> [(Name, Def Value Value)]
  -> Result [(Name, Def Value Value)]
checkEvalProgram [] evaledDefs = Right evaledDefs
checkEvalProgram (decl : decls) evaledDefs = do
  def <- checkDecl evaledDefs decl
  checkEvalProgram decls (def ++ evaledDefs)
