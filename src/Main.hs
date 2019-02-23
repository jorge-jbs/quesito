module Main where

import Quesito
import Quesito.LC.CodeGen
import qualified Quesito.TT as TT
import Quesito.TT.TopLevel as TT (typeAnn)
import qualified Quesito.Ann as Ann
import qualified Quesito.LC.TopLevel as LC
import qualified Quesito.Env as Env
import Quesito.Syntax as Syn (getNames, desugarDef)
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
        --declarations <- foldlM (\env def -> do def' <- Syn.desugar env def; return (Env.insert def' env)) emptyAnnEnv definitions
        let ttDefs = undefined :: [TT.Def]
        tell $ show ttDefs
        annDefs <- foldlM
          (\annDefs ttDef -> do
              annDef <- TT.typeAnn annDefs ttDef
              return (Env.insert annDef annDefs)
          )
          Env.empty
          ttDefs
        let decls = undefined :: [LC.Def]
        return (buildModuleT (fromString "main") (evalStateT (mapM defCodeGen decls) Map.empty))
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
