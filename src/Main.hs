module Main where

import Quesito
import Quesito.CodeGen
import Quesito.LLTT.TopLevel as LLTT (lowerDef)
import Quesito.TT.TopLevel as TT (typeAnn)
import qualified Quesito.Env as Env
import Quesito.Syntax as Syn
import Quesito.Syntax.Parse (parse)

import Data.Foldable (foldlM)
import Data.String (fromString)
import Data.Text.Lazy (unpack)
import LLVM.Pretty
import LLVM.IRBuilder.Module as L
import qualified LLVM.AST as L hiding (function)
import qualified LLVM.AST.AddrSpace as L

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
        return $ buildModuleT (fromString "main") $ do
          _ <- L.function
            (L.mkName "llvm.memcpy.p0i8.p0i8.i32")
            [ (L.PointerType (L.IntegerType 8) (L.AddrSpace 0), L.NoParameterName)
            , (L.PointerType (L.IntegerType 8) (L.AddrSpace 0), L.NoParameterName)
            , (L.IntegerType 32, L.NoParameterName)
            , (L.IntegerType 1, L.NoParameterName)
            ]
            L.VoidType
            (const $ return ())
          mapM (defGen llttDefs) llttDefs
  putStrLn w
  case m of
    Right m' ->
      putStrLn . unpack . ppllvm =<< m'
    Left err ->
      putStrLn ("Error compiling: " ++ err)
