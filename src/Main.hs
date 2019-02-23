module Main where

import Quesito
import Quesito.LC.CodeGen
import qualified Quesito.TT as TT
import Quesito.TT.TopLevel as TT (typeAnn)
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
        let declarations = undefined :: [TT.Def]
        tell $ show declarations
        decls <- reverse . fst <$> foldlM
          (\(decls, env) decl -> do
              (decl', env') <- TT.typeAnn env decl
              return (decl' : decls, env')
          )
          ([], Env.empty)
          declarations
        return (buildModuleT (fromString "main") (evalStateT (mapM defCodeGen decls) Map.empty))
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
