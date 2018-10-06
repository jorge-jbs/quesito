module Main where

import Quesito
import Quesito.TT (Name, Value, quote, Decl, Def(..), checkDecl)
import Quesito.Parse (parse)

main :: IO ()
main = do
  input <- getContents
  let
    declarations
      = either (error . show) id
      $ parse input
  case runQues $ head <$> checkEvalProgram declarations [] of
    Right (_, DMatchFunction [([], e)] _) ->
      putStrLn $ show $ quote (e [])
    Right _ ->
      putStrLn "The last expression of a source file must be a simple (non-pattern-matching) expression."
    Left err ->
      putStrLn ("Type checking failed: " ++ err)

checkEvalProgram :: [Decl] -> [(Name, Def Value Value)] -> Ques [(Name, Def Value Value)]
checkEvalProgram [] evaledDefs =
  return evaledDefs
checkEvalProgram (decl : decls) evaledDefs = do
  def <- checkDecl evaledDefs decl
  checkEvalProgram decls (def ++ evaledDefs)
