module Quesito.LC.CodeGen where

import Quesito
import Quesito.LC as LC
import Quesito.LC.TopLevel as LC
import qualified Quesito.TT.Eval as TT

import Data.String (fromString)
import Control.Monad (join)
import LLVM as L
import LLVM.AST as L hiding (function)
import LLVM.AST.Constant as L
import LLVM.AST.Global as L
import LLVM.IRBuilder.Instruction as L
import LLVM.IRBuilder.Module as L
import LLVM.IRBuilder.Monad as L

defCodeGen :: Decl -> ModuleBuilder ()
defCodeGen (ExprDecl name args t retTy) = do
  _ <- L.function
    (mkName name)
    ( map
        (\(argName, ty) ->
          (typeToLType ty, ParameterName (fromString argName))
        )
        args
    )
    (typeToLType retTy)
    (const (codeGen t >>= L.ret))
  return ()
defCodeGen (TypeDecl name cons) = do
  _ <- L.typedef (mkName name) Nothing
  flip mapM cons (\(name, consTy) -> do
      let (args, retTy) = flatten consTy
      _ <- L.function
        (mkName name)
        (map (\arg -> (gtypeToLType arg, L.NoParameterName)) args)
        (typeToLType retTy)
        (const (return ()))
      return ()
    )
  return ()
  where
    flatten :: LC.Type LC.Name -> ([GType], LC.Type LC.Name)
    flatten (Pi x arg t) =
      let (args, retTy) = flatten t
      in (arg : args, retTy)
    flatten t =
      ([], t)

codeGen :: Term LC.Name -> L.IRBuilderT ModuleBuilder L.Operand
codeGen (Bound v ty) =
  return (L.LocalReference (gtypeToLType ty) (mkName v))
codeGen (Free v ty) =
  return (L.ConstantOperand (L.GlobalReference (gtypeToLType ty) (mkName v)))
codeGen (Lit n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen (App v ty args) = do
  join $ L.call
    (L.ConstantOperand (L.GlobalReference (typeToLType ty) (mkName v)))
    <$> mapM (fmap (flip (,) []) . codeGen) args
codeGen (Ann t _) =
  codeGen t
-- codeGen (GType ty) = undefined

gtypeToLType :: GType -> L.Type
gtypeToLType (BytesType n) =
  L.IntegerType (fromIntegral (n*8))

typeToLType :: LC.Type LC.Name -> L.Type
typeToLType (GroundType ty) =
  gtypeToLType ty
typeToLType (TypeVar x) =
  NamedTypeReference (mkName x)
typeToLType ty@(Pi _ _ _) =
  let (args, ret) = flatten ty
  in L.FunctionType ret args False
  where
    flatten :: LC.Type LC.Name -> ([L.Type], L.Type)
    flatten (GroundType ty) =
      ([], gtypeToLType ty)
    flatten (Pi _ ty ty') =
      (gtypeToLType ty : args, ret)
      where
        (args, ret) = flatten ty'
