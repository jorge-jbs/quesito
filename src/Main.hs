module Main where

import Quesito
import Quesito.LC.CodeGen
import Quesito.TT.TopLevel (ttDeclToLcDecl)
import Quesito.Syntax (name, convertDef)
import Quesito.Syntax.Parse (parse)

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
        declarations <- snd <$> foldlM (\(env, decls) def -> do decl <- convertDef env def; return (name def:env, decls ++ [decl])) ([], []) definitions
        mapM_ (tell . (:[]) . show) declarations
        (decls, _) <- foldlM
          (\(decls, env) decl -> do
              (decl', env') <- ttDeclToLcDecl env decl
              return (decl' : decls, env')
          )
          ([], Map.empty)
          declarations
        return (buildModuleT (fromString "main") (mapM defCodeGen decls))
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
