module Main where

import Quesito
import Quesito.CodeGen
import Quesito.CodeGen.TopLevel
import Quesito.LLTT.TopLevel as LLTT (lowerDef)
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
        llttDefs <- foldlM
          (\llttDefs annDef -> do
              llttDef <- LLTT.lowerDef llttDefs annDef
              return $ Env.append llttDefs $ Env.fromList llttDef
          )
          Env.empty
          annDefs
        return $ buildModuleT (fromString "main") $ mapM (defGen llttDefs) llttDefs
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
