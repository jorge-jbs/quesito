{-# LANGUAGE RecursiveDo #-}

module Quesito.LC.CodeGen where

import Quesito.LC as LC
import Quesito.LC.TopLevel as LC

import Data.String (fromString)
import Data.Foldable (foldlM)
import Control.Monad (forM_, void)
import Control.Monad.IO.Class (liftIO)
import LLVM ()
import qualified LLVM.AST as L hiding (function)
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.Constant as L
import qualified LLVM.AST.DataLayout as L (defaultDataLayout, Endianness(LittleEndian))
import qualified LLVM.AST.IntegerPredicate as L
import qualified LLVM.AST.Type as L (Type(StructureType))
import qualified LLVM.Internal.Coding as L (encodeM)
import qualified LLVM.Internal.Context as L (withContext)
import qualified LLVM.Internal.DataLayout as L (withFFIDataLayout)
import qualified LLVM.Internal.EncodeAST as L (runEncodeAST)
import qualified LLVM.Internal.FFI.DataLayout as L (getTypeAllocSize)
import qualified LLVM.IRBuilder.Instruction as L
import qualified LLVM.IRBuilder.Module as L
import qualified LLVM.IRBuilder.Monad as L
import GHC.Word (Word32, Word64)

sizeOf :: L.Type -> IO Word64
sizeOf ty = L.withContext $ \ctx -> L.runEncodeAST ctx $ do
  ty' <- L.encodeM ty
  liftIO (L.withFFIDataLayout
    (L.defaultDataLayout L.LittleEndian)
    (\dl -> L.getTypeAllocSize dl ty'))

defCodeGen :: Decl -> L.ModuleBuilderT IO ()
defCodeGen (ExprDecl name args t retTy) = do
  _ <- L.function
    (L.mkName name)
    ( map
        (\(argName, ty) ->
          (typeToLType ty, L.ParameterName (fromString argName))
        )
        args
    )
    (typeToLType retTy)
    (const (codeGen t >>= L.ret))
  return ()
defCodeGen (PatternMatchingDecl name equations args retTy) = do
  let argsTypes = map (\ty -> (typeToLType ty, L.NoParameterName)) args
  _ <- L.function
    (L.mkName name)
    argsTypes
    (typeToLType retTy)
    (const (mdo
      checks <- mapM (genEquationIf . (\(_, x, _) -> x)) equations
      genIfs labels checks
      labels <- mapM (\(x, y, z) -> genBody x y z) equations
      return ()
    ))
  return ()
  where
    genIfs :: [L.Name] -> [L.Operand] -> L.IRBuilderT (L.ModuleBuilderT IO) ()
    genIfs x y =
      void $ genIfs' x y
      where
        genIfs' :: [L.Name] -> [L.Operand] -> L.IRBuilderT (L.ModuleBuilderT IO) L.Name
        genIfs' [] [] = do
          n <- L.block
          L.unreachable
          return n
        genIfs' (lb:lbs) (ch:chs) = mdo
          n <- L.block
          L.condBr ch lb lb'
          lb' <- genIfs' lbs chs
          return n

    genEquationIf :: [Pattern Name] -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
    genEquationIf ps = do
      checks <- mapM
        (uncurry checkArg)
        (zip
          ps
          (map
            (\(i, ty) -> L.LocalReference ty (L.UnName i))
            (zip [0..] (map typeToLType args))
          )
        )
      foldlM L.and (L.ConstantOperand (L.Int 1 1)) checks

    checkArg :: Pattern Name -> L.Operand -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
    checkArg (Binding _) op = do
      return (L.ConstantOperand (L.Int 1 1))
    checkArg (NumPat n b) op = do
      L.icmp L.EQ (L.ConstantOperand (L.Int (2^b) (fromIntegral n))) op
    checkArg (Constructor _ _) op = do
      undefined

    genBody :: [(Name, Type Name)] -> [Pattern Name] -> Term Name -> L.IRBuilderT (L.ModuleBuilderT IO) L.Name
    genBody = undefined

defCodeGen (TypeDecl name cons) = do
  let flattened = map (flatten . snd) cons
  let consLTypes = map consLType (map fst flattened)
  maxSize <- liftIO (maximum <$> mapM sizeOf consLTypes)
  _ <- L.typedef (L.mkName name) (Just (L.StructureType False [L.IntegerType 32, L.ArrayType maxSize (L.IntegerType 8)]))
  forM_ (zip (zip (zip [0..] consLTypes) flattened) cons) (\(((n, consLType), (args, retTy)), (name, consTy)) -> do
      --let (args, retTy) = flatten consTy
      _ <- if length args == 0 then
        L.global
          (L.mkName name)
          (typeToLType retTy)
          (L.Struct (Just (L.mkName name)) False  [L.Int 32 0, L.Array (L.IntegerType 8) (replicate (fromIntegral maxSize) (L.Int 8 0))])
      else
        L.function
          (L.mkName name)
          (map (\arg -> (gtypeToLType arg, L.NoParameterName)) args)
          (typeToLType retTy)
          (const (do
            z <- L.alloca consLType Nothing 0
            x <- constructor 0 (map gtypeToLType args) consLType
            L.store z 0 x
            w <- L.bitcast z (L.PointerType (L.ArrayType maxSize (L.IntegerType 8)) (L.AddrSpace 0))
            y <- L.insertValue (L.ConstantOperand (L.Undef (typeToLType retTy))) (L.ConstantOperand (L.Int 32 n)) [0]
            a <- L.load w 0
            L.ret =<< L.insertValue y a [1]
          ))
      return ()
    )
  return ()
  where
    flatten :: LC.Type LC.Name -> ([GType LC.Name], LC.Type LC.Name)
    flatten (Pi _ arg t) =
      let (args, retTy) = flatten t
      in (arg : args, retTy)
    flatten t =
      ([], t)

    consLType :: [GType LC.Name] -> L.Type
    consLType =
      L.StructureType False . map gtypeToLType

    constructor :: Word32 -> [L.Type] -> L.Type -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
    constructor _ [] ty =
      return (L.ConstantOperand (L.Undef ty))
    constructor n (arg:args) ty = do
      x <- constructor (n+1) args ty
      L.insertValue x (L.LocalReference arg (L.UnName (fromIntegral $ toInteger n))) [n]

codeGen :: LC.Term LC.Name -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
codeGen (Local v ty) =
  return (L.LocalReference (gtypeToLType ty) (L.mkName v))
codeGen (Global v ty) =
  L.load (L.ConstantOperand (L.GlobalReference (L.PointerType (gtypeToLType ty) (L.AddrSpace 0)) (L.mkName v))) 0
codeGen (Lit n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen (App v ty args) = do
  L.call
    (L.ConstantOperand (L.GlobalReference (typeToLType ty) (L.mkName v)))
    =<< mapM (fmap (flip (,) []) . codeGen) args

gtypeToLType :: GType LC.Name -> L.Type
gtypeToLType (BytesType n) =
  L.IntegerType (fromIntegral (n*8))
gtypeToLType (TypeVar x) =
  L.NamedTypeReference (L.mkName x)

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
