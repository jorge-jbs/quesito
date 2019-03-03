module Main where

import Quesito
import Quesito.CodeGen
import Quesito.CodeGen.TopLevel
import Quesito.TT.TopLevel as TT (typeAnn)
import qualified Quesito.Env as Env
import Quesito.Syntax as Syn
import Quesito.Syntax.Parse (parse)

import Data.Foldable (foldlM)
import Data.String (fromString)
import Data.Text.Lazy (unpack)
import LLVM.Pretty
import LLVM.IRBuilder.Module

main :: IO ()
main = do
  input <- getContents
  let
    definitions
      = either (error . show) id
      $ parse input
  let (m, w) = runQues $ do
        ttDefs <- foldlM
          (\env def -> do
              def' <- Syn.desugarDef env def
              return (Env.insert def' env)
          )
          Env.empty
          definitions
        tell $ show ttDefs
        annDefs <- foldlM
          (\annDefs ttDef -> do
              annDef <- TT.typeAnn annDefs ttDef
              return (Env.insert annDef annDefs)
          )
          Env.empty
          ttDefs
        return $ buildModuleT (fromString "main") $ runCodeGen $ mapM defGen annDefs
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
