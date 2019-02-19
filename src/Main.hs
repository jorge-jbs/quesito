module Main where

import Quesito
import Quesito.LC.CodeGen
import Quesito.TT.TopLevel as TT (convertDef)
import Quesito.Syntax as Syn (getNames, convertDef)
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
        declarations <- snd <$> foldlM (\(env, decls) def -> do decl <- Syn.convertDef env def; return (getNames def ++ env, decls ++ [decl])) ([], []) definitions
        mapM_ (tell . show) declarations
        decls <- reverse . fst <$> foldlM
          (\(decls, env) decl -> do
              (decl', env') <- TT.convertDef env decl
              return (decl' : decls, env')
          )
          ([], Map.empty)
          declarations
        return (buildModuleT (fromString "main") (evalStateT (mapM defCodeGen decls) Map.empty))
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
