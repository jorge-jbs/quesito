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
  let (x, w) = runQues $ head <$> checkEvalProgram declarations []
  putStrLn w
  case x of
    Right (_, DMatchFunction [([], e)] _) -> do
      case runQues (quote =<< e []) of
        (Right qe, w') -> do
          putStrLn w'
          putStrLn $ show qe
        (Left err, w') -> do
          putStrLn w'
          putStrLn ("Error: " ++ err)
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
