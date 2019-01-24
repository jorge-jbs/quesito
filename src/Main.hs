module Main where

import Quesito
import Quesito.LC.CodeGen
import Quesito.TT.TopLevel(ttDeclToLcDecl)
import Quesito.Parse (parse)

import Data.Foldable (foldlM)
import Data.Text.Lazy (unpack)
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
        mapM_ (tell . (:[]) . show) declarations
        (decls, _) <- foldlM
          (\(decls, env) decl -> do
              (decl', env') <- ttDeclToLcDecl env decl
              return (decl' : decls, env')
          )
          ([], [])
          declarations
        return (buildModuleT (fromString "main") (mapM defCodeGen decls))
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
