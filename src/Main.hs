module Main where

import Quesito
import Quesito.LC.CodeGen
import Quesito.TT.TopLevel as TT (typeAnn)
import qualified Quesito.Ann.TopLevel as Ann
import qualified Quesito.Env as Env
import Quesito.Syntax as Syn
import Quesito.Syntax.Parse (parse)

import Control.Monad.State (evalStateT)
import Data.Foldable (foldlM)
import qualified Data.Map as Map
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
        ttDefs <- foldlM (\env def -> do def' <- Syn.desugarDef env def; return (Env.insert def' env)) Env.empty definitions
        tell $ show ttDefs
        annDefs <- foldlM
          (\annDefs ttDef -> do
              annDef <- TT.typeAnn annDefs ttDef
              return (Env.insert annDef annDefs)
          )
          Env.empty
          ttDefs
        lcDefs <- mapM Ann.convert annDefs
        return (buildModuleT (fromString "main") (evalStateT (mapM defCodeGen lcDefs) Map.empty))
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
