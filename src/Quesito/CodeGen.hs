{-# LANGUAGE RecursiveDo, FlexibleContexts, LambdaCase #-}

module Quesito.CodeGen where

import Prelude hiding (lookup)

import Quesito.CodeGen.TopLevel
import qualified Quesito.LC as LC
import qualified Quesito.LC.TopLevel as LC
import qualified Quesito.TT as TT

import Control.Monad (forM, forM_, void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans (lift)
import Data.Foldable (foldlM)
import Data.List (find, zip4)
import qualified Data.Map as Map
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
import qualified LLVM.IRBuilder.Monad as L
import GHC.Word (Word32, Word64)

sizeOf :: L.Type -> IO Word64
sizeOf ty = L.withContext $ \ctx -> L.runEncodeAST ctx $ do
  ty' <- L.encodeM ty
  liftIO (L.withFFIDataLayout
    (L.defaultDataLayout L.LittleEndian)
    (\dl -> L.getTypeAllocSize dl ty'))

type CodeGenState = Map.Map String Int

defCodeGen :: MonadCodeGen m => LC.Def -> m ()
defCodeGen (LC.PatternMatchingDef name equations args retTy _) = do
  function
    name
    (map typeToLType args)
    (typeToLType retTy)
    (void $ genEquations equations)
  return ()
  where
    genEquations :: MonadCodeGen m => [([(String, LC.Type)], [LC.Pattern], LC.Term)] -> L.IRBuilderT m L.Name
    genEquations [] =
      L.block <* L.unreachable
    genEquations ((vars, patterns, body):es) = mdo
      lb <- genEquation vars patterns body lb'
      lb' <- genEquations es
      return lb

    genEquation :: MonadCodeGen m => [(String, LC.Type)] -> [LC.Pattern] -> LC.Term -> L.Name -> L.IRBuilderT m L.Name
    genEquation vars patterns body lb = mdo
      n <- L.block
      b <- genEquationIf patterns
      L.condBr b lb' lb
      lb' <- genBody vars patterns body
      return n

    genEquationIf :: MonadCodeGen m => [LC.Pattern] -> L.IRBuilderT m L.Operand
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

    checkArg :: MonadCodeGen m => LC.Pattern -> L.Operand -> L.IRBuilderT m L.Operand
    checkArg (LC.Binding _) _ = do
      return (L.ConstantOperand (L.Int 1 1))
    checkArg (LC.NumPat n b) op = do
      L.icmp L.EQ (L.ConstantOperand (L.Int (fromIntegral (b*8)) (fromIntegral n))) op
    checkArg (LC.Constructor consName _) op = do
      def <- lift (lookup consName)
      let n = case def of
            Just (Constructor _ _ tag _) ->
              tag
            _ ->
              error ""
      m <- L.extractValue op [0]
      L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral n) m

    bindArg
      :: MonadCodeGen m
      => LC.Pattern
      -> L.Operand
      -> L.IRBuilderT m [(String, L.Operand)]
    bindArg (LC.Binding x) op = do
      return [(x, op)]
    bindArg (LC.NumPat _ _) _ = do
      return []
    bindArg (LC.Constructor _ []) _ = do
      return []
    bindArg (LC.Constructor name args) op = do
      def <- lift $ lookup name
      case def of
        Just (Constructor _ retTy _ (FunctionConstructor _ ty)) -> do
          ptr <- L.alloca retTy Nothing 0
          L.store ptr 0 op
          ptr' <- L.bitcast
            ptr
            (L.PointerType
              (L.StructureType
                False
                [L.IntegerType 32, ty]
              )
              (L.AddrSpace 0)
            )
          deptr <- L.load ptr' 0
          concat <$> forM (zip [0..] args) (\(i, arg) -> do
              op' <- L.extractValue deptr [1, i]
              bindArg arg op'
            )
        _ -> error ""

    genBody :: MonadCodeGen m => [(String, LC.Type)] -> [LC.Pattern] -> LC.Term -> L.IRBuilderT m L.Name
    genBody _ patterns t = do
      n <- L.block
      boundArgs <- foldl (++) [] <$> (mapM (uncurry bindArg) (zip patterns
        (map
          (\(i, ty) -> L.LocalReference ty (L.UnName i))
          (zip [0..] (map typeToLType args))
        )))
      L.ret =<< codeGen boundArgs t
      return n
defCodeGen (LC.TypeDef name cons) = do
  let flattened = map (flatten . snd) cons
  let getConsLTypes = map getConsLType (map fst flattened)
  maxSize <- liftIO (maximum <$> mapM sizeOf getConsLTypes)
  typeDef
    name
    (L.StructureType
      False
      [L.IntegerType 32, L.ArrayType maxSize (L.IntegerType 8)]
    )
  forM_ (zip4 [0..] getConsLTypes flattened (map fst cons)) (\(n, consLType, (args, retTy), consName) -> do
      if length args == 0 then
        emptyConstructor consName (typeToLType retTy) n maxSize
      else
        functionConstructor
          consName
          (map gtypeToLType args)
          consLType
          (typeToLType retTy)
          n
          (do
            z <- L.alloca consLType Nothing 0
            x <- constructor 0 (map gtypeToLType args) consLType
            L.store z 0 x
            w <- L.bitcast z (L.PointerType (L.ArrayType maxSize (L.IntegerType 8)) (L.AddrSpace 0))
            y <- L.insertValue (L.ConstantOperand (L.Undef (typeToLType retTy))) (L.ConstantOperand (L.Int 32 n)) [0]
            a <- L.load w 0
            L.ret =<< L.insertValue y a [1]
          )
      return ()
    )
  return ()
  where
    flatten :: LC.Type -> ([LC.GType], LC.Type)
    flatten (LC.Pi _ arg t) =
      let (args, retTy) = flatten t
      in (arg : args, retTy)
    flatten t =
      ([], t)

    getConsLType :: [LC.GType] -> L.Type
    getConsLType =
      L.StructureType False . map gtypeToLType

    constructor :: (MonadCodeGen m) => Word32 -> [L.Type] -> L.Type -> L.IRBuilderT m L.Operand
    constructor _ [] ty =
      return (L.ConstantOperand (L.Undef ty))
    constructor n (arg:args) ty = do
      x <- constructor (n+1) args ty
      L.insertValue x (L.LocalReference arg (L.UnName (fromIntegral $ toInteger n))) [n]

codeGen :: (MonadCodeGen m) => [(String, L.Operand)] -> LC.Term -> L.IRBuilderT m L.Operand
codeGen env (LC.Local v ty) =
  case snd <$> find ((==) v . fst) env of
    Just op ->
      return op
    Nothing ->
      return (L.LocalReference (gtypeToLType ty) (L.mkName v))
codeGen _ (LC.Global v ty) =
  L.load (L.ConstantOperand (L.GlobalReference (L.PointerType (gtypeToLType ty) (L.AddrSpace 0)) (L.mkName v))) 0
codeGen _ (LC.Lit n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env (LC.App v ty args) = do
  L.call
    (L.ConstantOperand (L.GlobalReference (typeToLType ty) (L.mkName v)))
    =<< mapM (fmap (flip (,) []) . codeGen env) args
codeGen env (LC.BinOp op a b) =
  let instr =
        case op of
          TT.Add -> L.add
          TT.Sub -> L.sub
          TT.Mul -> L.mul
          _ -> undefined
  in do
    a' <- codeGen env a
    b' <- codeGen env b
    instr a' b'
codeGen _ (LC.UnOp TT.Not _) =
  undefined

gtypeToLType :: LC.GType -> L.Type
gtypeToLType (LC.BytesType n) =
  L.IntegerType (fromIntegral (n*8))
gtypeToLType (LC.TypeVar x) =
  L.NamedTypeReference (L.mkName x)

typeToLType :: LC.Type -> L.Type
typeToLType (LC.GroundType ty) =
  gtypeToLType ty
typeToLType ty@(LC.Pi _ _ _) =
  let (args, ret) = flatten ty
  in L.FunctionType ret args False
  where
    flatten :: LC.Type -> ([L.Type], L.Type)
    flatten (LC.GroundType ty') =
      ([], gtypeToLType ty')
    flatten (LC.Pi _ ty1 ty2) =
      (gtypeToLType ty1 : args, ret)
      where
        (args, ret) = flatten ty2
