{-# LANGUAGE RecursiveDo, FlexibleContexts, LambdaCase #-}

module Quesito.CodeGen where

import Prelude hiding (lookup)
import qualified Prelude
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Fix (MonadFix)
import Data.Word (Word64)

import Quesito
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env
import qualified Quesito.LLTT as LLTT
import qualified Quesito.TT as TT

import Control.Monad (forM, forM_, void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans (lift)
import Data.Foldable (foldlM)
import Data.List (find, zip4)
import Data.Maybe (fromJust)
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

getSize
  :: (L.MonadModuleBuilder m, L.MonadIRBuilder m)
  => LLTT.Type
  -> L.Operand
  -> [(String, L.Operand)]
  -> m L.Operand
getSize (LLTT.BytesType n) _ _ =
  return $ L.ConstantOperand $ L.Int 32 $ fromIntegral n
getSize (LLTT.Type _) op _ =
  return $ L.ConstantOperand $ L.Int 32 4
getSize (LLTT.Constant (LLTT.TypeCons v ty)) op env = do
  L.call
    ( L.ConstantOperand
    $ L.GlobalReference
        (L.FunctionType
          (L.IntegerType 32)
          [L.PointerType (L.IntegerType 8) (L.AddrSpace 0)]
          False
        )
        (L.mkName v)
    )
    [(op, [])]
getSize (LLTT.Constant (LLTT.Local v _)) op env = do
  let f = fromJust $ Prelude.lookup v env
  f' <- L.bitcast f
    $ flip L.PointerType (L.AddrSpace 0)
    $ flip L.PointerType (L.AddrSpace 0)
    $ L.FunctionType
        (L.IntegerType 32)
        [L.PointerType (L.IntegerType 8) (L.AddrSpace 0)]
        False
  f'' <- L.load f' 0
  L.call f'' [(op, [])]
getSize (LLTT.Constant (LLTT.Global v ty)) op _ =
  L.call
    ( L.ConstantOperand
    $ L.GlobalReference
        (L.FunctionType
          (L.IntegerType 32)
          [L.PointerType (L.IntegerType 8) (L.AddrSpace 0)]
          False
        )
        (L.mkName v)
    )
    [(op, [])]
getSize (LLTT.Call v _) op env =
  getSize (LLTT.Constant v) op env
getSize t _ _ =
  error $ show t

sizeOf :: L.Type -> IO Word64
sizeOf ty = L.withContext $ \ctx -> L.runEncodeAST ctx $ do
  ty' <- L.encodeM ty
  liftIO (L.withFFIDataLayout
    (L.defaultDataLayout L.LittleEndian)
    (\dl -> L.getTypeAllocSize dl ty'))

function
  :: L.MonadModuleBuilder m
  => String
  -> [L.Type]
  -> L.Type
  -> L.IRBuilderT m ()
  -> m ()
function name argsTys retTy body = do
  _ <- L.function
    (L.mkName name)
    (map (flip (,) L.NoParameterName) argsTys)
    retTy
    (const body)
  return ()

typeDef name body = do
  _ <- L.function
    (L.mkName name)
    [(L.PointerType (L.IntegerType 8) (L.AddrSpace 0), L.NoParameterName)]
    (L.IntegerType 32)
    (\[op] -> body op)
  return ()

patGen
  :: (L.MonadModuleBuilder m, L.MonadIRBuilder m)
  => LLTT.Env
  -> Ann.Pattern
  -> L.Operand
  -> m (L.Operand, [(String, L.Operand)])
patGen _ (Ann.Binding x) op =
  return (L.ConstantOperand (L.Int 1 1), [(x, op)])
patGen _ (Ann.Inaccessible _) _ =
  undefined
patGen _ (Ann.NumPat n b) op = do
  x <- L.icmp L.EQ (L.ConstantOperand (L.Int (fromIntegral (b*8)) (fromIntegral n))) op
  return (x, [])
patGen env (Ann.Constructor consName) op = do
  let tag = case Env.lookup consName env of
        Just (LLTT.ConstructorDef _ _ tag') ->
          tag'
        _ ->
          error ""
  tagPtr <- L.bitcast op $ flip L.PointerType (L.AddrSpace 0) $ L.IntegerType 32
  tagOp <- L.load tagPtr 0
  b <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral tag) tagOp
  return (b, [])
patGen env p@(Ann.PatApp _ _) op = case Ann.flattenPatApp p of
  Ann.Constructor consName : args -> do
    case Env.lookup consName env of
      Just (LLTT.ConstructorDef _ ty tag) -> do
        tagPtr <-
          L.bitcast op $ flip L.PointerType (L.AddrSpace 0) $ L.IntegerType 32
        tagOp <- L.load tagPtr 0
        b1 <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral tag) tagOp
        op' <- L.gep op [L.ConstantOperand $ L.Int 32 4]
        (b2, binds) <- deconstruct ty args op' []
        b <- L.and b1 b2
        return (b, binds)
      _ -> error ""
  _ -> error ""
  where
    deconstruct (LLTT.Pi v ty1 ty2) (arg:args) op sizeEnv = do
      (b1, binds1) <- patGen env arg op
      size <- codeGen sizeEnv ty1
      op' <- L.gep op [size]
      (b2, binds2) <- deconstruct ty2 args op' ((v, op) : sizeEnv)
      b <- L.and b1 b2
      return (b, binds1 ++ binds2)
    deconstruct _ [] _ _ =
      return (L.ConstantOperand $ L.Int 1 1, [])

defGen
  :: (L.MonadModuleBuilder m, MonadFix m)
  => LLTT.Env
  -> LLTT.Def
  -> m ()
defGen env (LLTT.PatternMatchingDef name equations ty) = do
  let (args, retTy) = LLTT.flattenPi ty
  args' <- mapM typeGen args
  retTy' <- typeGen retTy
  function
    name
    args'
    retTy'
    (void $ genEquations args' equations)
  return ()
  where
    genEquations
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [L.Type]
      -> [([(String, LLTT.Type)], [Ann.Pattern], LLTT.Term)]
      -> L.IRBuilderT m L.Name
    genEquations _ [] =
      L.block <* L.unreachable
    genEquations args' ((_, patterns, body):es) = mdo
      lb <- genEquation args' patterns body lb'
      lb' <- genEquations args' es
      return lb

    genEquation
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [L.Type]
      -> [Ann.Pattern]
      -> LLTT.Term
      -> L.Name
      -> L.IRBuilderT m L.Name
    genEquation args' patterns body lb = mdo
      n <- L.block
      xs <-
        mapM
          (uncurry $ patGen env)
          (zip
            patterns
            (map
              (\(i, argTy) -> L.LocalReference argTy (L.UnName i))
              (zip [0..] args')))
      b <- foldlM L.and (L.ConstantOperand (L.Int 1 1)) (map fst xs)
      L.condBr b lb' lb
      lb' <- L.block
      let boundArgs = foldl (++) [] (map snd xs)
      L.ret =<< codeGen boundArgs body
      return n
defGen env (LLTT.TypeDef name equations ty) = do
  let (args, retTy) = LLTT.flattenPi ty
  args' <- mapM typeGen args
  retTy' <- typeGen retTy
  function
    name
    args'
    retTy'
    (void $ genEquations args' equations)
  return ()
  where
    genEquations
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [L.Type]
      -> [([(String, LLTT.Type)], [Ann.Pattern], [LLTT.Type])]
      -> L.IRBuilderT m L.Name
    genEquations _ [] =
      L.block <* L.unreachable
    genEquations args' ((_, patterns, body):es) = mdo
      lb <- genEquation args' patterns body lb'
      lb' <- genEquations args' es
      return lb

    genEquation
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [L.Type]
      -> [Ann.Pattern]
      -> [LLTT.Type]
      -> L.Name
      -> L.IRBuilderT m L.Name
    genEquation args' patterns body lb = mdo
      n <- L.block
      xs <-
        mapM
          (uncurry $ patGen env)
          (zip
            patterns
            (map
              (\(i, argTy) -> L.LocalReference argTy (L.UnName i))
              (zip [0..] args')))
      b <- foldlM L.and (L.ConstantOperand (L.Int 1 1)) (map fst xs)
      L.condBr b lb' lb
      lb' <- L.block
      let boundArgs = foldl (++) [] (map snd xs)
      body' <- foldlM (\acc x -> do
            x' <- codeGen boundArgs x
            L.add x' acc
          )
          (L.ConstantOperand $ L.Int 32 0)
          body
      L.ret body'
      return n
defGen _ (LLTT.ConstructorDef name _ _) = do
  typeDef
    name
    (\op -> mdo
      return ()
    )

codeGen
  :: (L.MonadModuleBuilder m, L.MonadIRBuilder m)
  => [(String, L.Operand)]
  -> LLTT.Term
  -> m L.Operand
codeGen env (LLTT.Constant (LLTT.Local v ty)) = do
  case snd <$> find ((==) v . fst) env of
    Just op ->
      return op
    Nothing -> do
      ty' <- typeGen ty
      return $ L.LocalReference ty' $ L.mkName v
codeGen _ (LLTT.Constant (LLTT.Global v ty)) = do
  ty' <- typeGen ty
  L.load
    ( L.ConstantOperand
    $ L.GlobalReference (L.PointerType ty' $ L.AddrSpace 0)
    $ L.mkName v
    )
    0
codeGen _ (LLTT.Constant (LLTT.TypeCons v ty)) = do
  ty' <- typeGen ty
  L.call
    (L.ConstantOperand $ L.GlobalReference (L.FunctionType ty' [] False) $ L.mkName v)
    []
codeGen _ (LLTT.Num n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env (LLTT.Call (LLTT.TypeCons v ty) args) =
  codeGen env $ LLTT.Call (LLTT.Global v ty) args
codeGen env (LLTT.Call (LLTT.Constructor v ty) args) = do
  codeGen env $ LLTT.Call (LLTT.Global v ty) args
codeGen env (LLTT.Call (LLTT.Global v ty) args) = do
  ty' <- typeGen ty
  L.call
    (L.ConstantOperand $ L.GlobalReference ty' $ L.mkName v)
    =<< mapM (fmap (flip (,) []) . codeGen env) args
codeGen _ (LLTT.Call _ _) = do
  error ""
codeGen env (LLTT.BinOp op a b) = do
  let instr = case op of
        TT.Add -> L.add
        TT.Sub -> L.sub
        TT.Mul -> L.mul
        _ -> undefined
  a' <- codeGen env a
  b' <- codeGen env b
  instr a' b'
codeGen _ (LLTT.UnOp _ _) = do
  undefined
codeGen _ (LLTT.BytesType n) = do
  return $ L.ConstantOperand $ L.Int 32 $ fromIntegral n
codeGen _ (LLTT.Type _) = do
  return $ L.ConstantOperand $ L.Int 32 4
codeGen _ t =
  error $ show t

typeGen :: L.MonadModuleBuilder m => LLTT.Type -> m L.Type

typeGen ty@(LLTT.Pi _ _ _) =
  let (args, ret) = LLTT.flattenPi ty
  in L.FunctionType <$> typeGen ret <*> mapM typeGen args <*> pure False
typeGen (LLTT.BytesType n) =
  return $ L.IntegerType $ fromIntegral (n*8)
typeGen (LLTT.Type _) = do
  return $ L.IntegerType 32
typeGen (LLTT.Constant _) = do
  return $ L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
typeGen (LLTT.Call v _) =
  typeGen $ LLTT.Constant v
typeGen t =
  error $ show t
