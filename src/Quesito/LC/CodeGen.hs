{-# LANGUAGE RecursiveDo #-}

module Quesito.LC.CodeGen where

import Quesito.LC as LC
import Quesito.LC.TopLevel as LC
import qualified Quesito.TT as TT

import Data.Foldable (foldlM)
import Data.List (find, zip4)
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
defCodeGen (PatternMatchingDecl name equations args retTy _) = do
  let argsTypes = map (\ty -> (typeToLType ty, L.NoParameterName)) args
  _ <- L.function
    (L.mkName name)
    argsTypes
    (typeToLType retTy)
    (const . void $ genEquations equations)
  return ()
  where
    genEquations :: [([(String, Type)], [Pattern], Term)] -> L.IRBuilderT (L.ModuleBuilderT IO) L.Name
    genEquations [] =
      L.block <* L.unreachable
    genEquations ((vars, patterns, body):es) = mdo
      lb <- genEquation vars patterns body lb'
      lb' <- genEquations es
      return lb

    genEquation :: [(String, Type)] -> [Pattern] -> Term -> L.Name -> L.IRBuilderT (L.ModuleBuilderT IO) L.Name
    genEquation vars patterns body lb = mdo
      n <- L.block
      b <- genEquationIf patterns
      L.condBr b lb' lb
      lb' <- genBody vars patterns body
      return n

    genEquationIf :: [Pattern] -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
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

    checkArg :: Pattern -> L.Operand -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
    checkArg (Binding _) _ = do
      return (L.ConstantOperand (L.Int 1 1))
    checkArg (NumPat n b) op = do
      L.icmp L.EQ (L.ConstantOperand (L.Int (fromIntegral (b*8)) (fromIntegral n))) op
    checkArg (Constructor _ _) _ = do
      undefined

    bindArg :: Pattern -> L.Operand -> L.IRBuilderT (L.ModuleBuilderT IO) [(String, L.Operand)]
    bindArg (Binding x) op = do
      return [(x, op)]
    bindArg (NumPat _ _) _ = do
      return []
    bindArg (Constructor _ _) _ = do
      undefined

    genBody :: [(String, Type)] -> [Pattern] -> Term -> L.IRBuilderT (L.ModuleBuilderT IO) L.Name
    genBody _ patterns t = do
      n <- L.block
      boundArgs <- foldl (++) [] <$> (mapM (uncurry bindArg) (zip patterns
        (map
          (\(i, ty) -> L.LocalReference ty (L.UnName i))
          (zip [0..] (map typeToLType args))
        )))
      L.ret =<< codeGen boundArgs t
      return n

defCodeGen (TypeDecl name cons) = do
  let flattened = map (flatten . snd) cons
  let getConsLTypes = map getConsLType (map fst flattened)
  maxSize <- liftIO (maximum <$> mapM sizeOf getConsLTypes)
  _ <- L.typedef (L.mkName name) (Just (L.StructureType False [L.IntegerType 32, L.ArrayType maxSize (L.IntegerType 8)]))
  forM_ (zip4 [0..] getConsLTypes flattened (map fst cons)) (\(n, consLType, (args, retTy), consName) -> do
      _ <- if length args == 0 then
        L.global
          (L.mkName consName)
          (typeToLType retTy)
          (L.Struct (Just (L.mkName consName)) False  [L.Int 32 n, L.Array (L.IntegerType 8) (replicate (fromIntegral maxSize) (L.Int 8 0))])
      else
        L.function
          (L.mkName consName)
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
    flatten :: LC.Type -> ([GType], LC.Type)
    flatten (Pi _ arg t) =
      let (args, retTy) = flatten t
      in (arg : args, retTy)
    flatten t =
      ([], t)

    getConsLType :: [GType] -> L.Type
    getConsLType =
      L.StructureType False . map gtypeToLType

    constructor :: Word32 -> [L.Type] -> L.Type -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
    constructor _ [] ty =
      return (L.ConstantOperand (L.Undef ty))
    constructor n (arg:args) ty = do
      x <- constructor (n+1) args ty
      L.insertValue x (L.LocalReference arg (L.UnName (fromIntegral $ toInteger n))) [n]

codeGen :: [(String, L.Operand)] -> LC.Term -> L.IRBuilderT (L.ModuleBuilderT IO) L.Operand
codeGen env (Local v ty) =
  case snd <$> find ((==) v . fst) env of
    Just op ->
      return op
    Nothing ->
      return (L.LocalReference (gtypeToLType ty) (L.mkName v))
codeGen _ (Global v ty) =
  L.load (L.ConstantOperand (L.GlobalReference (L.PointerType (gtypeToLType ty) (L.AddrSpace 0)) (L.mkName v))) 0
codeGen _ (Lit n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env (App v ty args) = do
  L.call
    (L.ConstantOperand (L.GlobalReference (typeToLType ty) (L.mkName v)))
    =<< mapM (fmap (flip (,) []) . codeGen env) args
codeGen env (BinOp op a b) =
  let instr =
        case op of
          TT.Add -> L.add
          TT.Sub -> L.sub
          _ -> undefined
  in do
    a' <- codeGen env a
    b' <- codeGen env b
    instr a' b'
codeGen _ (UnOp TT.Not _) =
  undefined

gtypeToLType :: GType -> L.Type
gtypeToLType (BytesType n) =
  L.IntegerType (fromIntegral (n*8))
gtypeToLType (TypeVar x) =
  L.NamedTypeReference (L.mkName x)

typeToLType :: LC.Type -> L.Type
typeToLType (GroundType ty) =
  gtypeToLType ty
typeToLType ty@(Pi _ _ _) =
  let (args, ret) = flatten ty
  in L.FunctionType ret args False
  where
    flatten :: LC.Type -> ([L.Type], L.Type)
    flatten (GroundType ty') =
      ([], gtypeToLType ty')
    flatten (Pi _ ty1 ty2) =
      (gtypeToLType ty1 : args, ret)
      where
        (args, ret) = flatten ty2
