module Main where

import Quesito
import Quesito.TT (Name)
import Quesito.TT.CodeGen
import Quesito.TT.Eval (Value, Def(..), quote)
import Quesito.TT.TopLevel (Decl, checkDecl)
import Quesito.TopLevel
import Quesito.Parse (parse)

import Data.String (fromString)
import LLVM.Pretty
import LLVM.IRBuilder.Module

main :: IO ()
main = do
  input <- getContents
  let
    declarations
      = either (error . show) id
      $ parse input
  let (m, w) = runQues $ do
        decls <- mapM declToLcDecl declarations
        buildModuleT
          (fromString "main")
          (mapM
            (\(name, args, body, retTy) ->
              defCodeGen name args body retTy
            )
            decls
          )
  putStrLn w
  case m of
    Right mod ->
      putStrLn $ show $ ppllvm mod
    Left err ->
      putStrLn ("Error compiling: " ++ err)
  -- let (x, w) = runQues $ head <$> checkEvalProgram declarations []
  -- putStrLn w
  -- case x of
  --   Right (_, DMatchFunction [([], e)] _) -> do
  --     case runQues (quote =<< e []) of
  --       (Right qe, w') -> do
  --         putStrLn w'
  --         putStrLn $ show qe
  --         putStrLn "\n"
  --       (Left err, w') -> do
  --         putStrLn w'
  --         putStrLn ("Error: " ++ err)
  --   Right _ ->
  --     putStrLn "The last expression of a source file must be a simple (non-pattern-matching) expression."
  --   Left err ->
  --     putStrLn ("Type checking failed: " ++ err)

checkEvalProgram :: [Decl] -> [(Name, Def Value Value)] -> Ques [(Name, Def Value Value)]
checkEvalProgram [] evaledDefs =
  return evaledDefs
checkEvalProgram (decl : decls) evaledDefs = do
  def <- checkDecl evaledDefs decl
  checkEvalProgram decls (def ++ evaledDefs)
