module Quesito.TT.CodeGen where

import Quesito
import Quesito.LC as LC

import Control.Monad (join)
import LLVM as L
import LLVM.AST as L
import LLVM.AST.Constant as L
import LLVM.IRBuilder.Instruction as L
import LLVM.IRBuilder.Module as L
import LLVM.IRBuilder.Monad as L

codeGen :: Term LC.Name -> L.IRBuilderT Ques L.Operand
codeGen (Var v ty) =
  return (L.LocalReference (gtypeToLType ty) (mkName v))
codeGen (Lit n) =
  return (L.ConstantOperand (L.Int 128 (fromIntegral n)))
codeGen (App v ty args) = do
  join $ L.call
    (L.ConstantOperand (L.GlobalReference (typeToLType ty) (mkName v)))
    <$> mapM (fmap (flip (,) []) . codeGen) args
codeGen (Ann t _) =
  codeGen t
-- codeGen (GType ty) = undefined

gtypeToLType :: GType -> L.Type
gtypeToLType (BytesType n) =
  L.IntegerType (fromIntegral n)

typeToLType :: LC.Type LC.Name -> L.Type
typeToLType (GroundType ty) =
  gtypeToLType ty
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
