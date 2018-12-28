module Quesito.LC.CodeGen where

import Quesito
import Quesito.LC as LC
import Quesito.LC.TopLevel as LC
import qualified Quesito.TT.Eval as TT

import Data.String (fromString)
import Control.Monad (join)
import Control.Monad.IO.Class (liftIO)
import LLVM as L
import LLVM.AST as L hiding (function)
import LLVM.AST.AddrSpace as L
import LLVM.AST.Constant as L
import LLVM.AST.DataLayout as L (defaultDataLayout, Endianness(LittleEndian))
import LLVM.AST.Global as L
import LLVM.AST.Type as L (Type(StructureType))
import LLVM.Internal.Coding as L (encodeM)
import LLVM.Internal.Context as L (withContext)
import LLVM.Internal.DataLayout as L (withFFIDataLayout)
import LLVM.Internal.EncodeAST as L (runEncodeAST)
import LLVM.Internal.FFI.DataLayout as L (getTypeAllocSize)
import LLVM.IRBuilder.Instruction as L
import LLVM.IRBuilder.Module as L
import LLVM.IRBuilder.Monad as L
import GHC.Word (Word32, Word64)

sizeOf :: L.Type -> IO Word64
sizeOf ty = L.withContext $ \ctx -> L.runEncodeAST ctx $ do
  ty <- encodeM ty
  liftIO (L.withFFIDataLayout
    (L.defaultDataLayout L.LittleEndian)
    (\dl -> L.getTypeAllocSize dl ty))

defCodeGen :: Decl -> ModuleBuilderT IO ()
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
  let flattened = map (flatten . snd) cons
  let consLTypes = map consLType (map fst flattened)
  maxSize <- liftIO (maximum <$> mapM sizeOf consLTypes)
  _ <- L.typedef (mkName name) (Just (L.StructureType False [L.IntegerType 32, L.ArrayType maxSize (L.IntegerType 8)]))
  flip mapM (zip (zip (zip [0..] consLTypes) flattened) cons) (\(((n, consLType), (args, retTy)), (name, consTy)) -> do
      --let (args, retTy) = flatten consTy
      _ <- if length args == 0 then
        L.global
          (mkName name)
          (typeToLType retTy)
          (L.Struct (Just (mkName name)) False  [L.Int 32 0, L.Array (L.IntegerType 8) (replicate (fromIntegral maxSize) (L.Int 8 0))])
      else
        L.function
          (mkName name)
          (map (\arg -> (gtypeToLType arg, L.NoParameterName)) args)
          (typeToLType retTy)
          (const (do
            z <- alloca consLType Nothing 0
            x <- constructor 0 (map gtypeToLType args) consLType
            store z 0 x
            w <- bitcast z (L.PointerType (L.ArrayType maxSize (L.IntegerType 8)) (L.AddrSpace 0))
            y <- insertValue (ConstantOperand (Undef (typeToLType retTy))) (ConstantOperand (Int 32 n)) [0]
            a <- load w 0
            ret =<< insertValue y a [1]
          ))
      return ()
    )
  return ()
  where
    flatten :: LC.Type LC.Name -> ([GType LC.Name], LC.Type LC.Name)
    flatten (Pi x arg t) =
      let (args, retTy) = flatten t
      in (arg : args, retTy)
    flatten t =
      ([], t)

    consLType :: [GType LC.Name] -> L.Type
    consLType =
      L.StructureType False . map gtypeToLType

    constructor :: Word32 -> [L.Type] -> L.Type -> L.IRBuilderT (ModuleBuilderT IO) L.Operand
    constructor _ [] ty =
      return (ConstantOperand (Undef ty))
    constructor n (arg:args) ty = do
      x <- constructor (n+1) args ty
      insertValue x (LocalReference arg (UnName (fromIntegral $ toInteger n))) [n]

codeGen :: LC.Term LC.Name -> L.IRBuilderT (ModuleBuilderT IO) L.Operand
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

gtypeToLType :: GType LC.Name -> L.Type
gtypeToLType (BytesType n) =
  L.IntegerType (fromIntegral (n*8))
gtypeToLType (TypeVar x) =
  NamedTypeReference (mkName x)

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
