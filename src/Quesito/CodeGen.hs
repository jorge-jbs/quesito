{-# LANGUAGE RecursiveDo #-}

module Quesito.CodeGen where

import Prelude hiding (lookup)
import qualified Prelude
import Control.Monad (zipWithM)
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
import qualified LLVM.AST.Type as L
import qualified LLVM.Internal.Coding as L (encodeM)
import qualified LLVM.Internal.Context as L (withContext)
import qualified LLVM.Internal.DataLayout as L (withFFIDataLayout)
import qualified LLVM.Internal.EncodeAST as L (runEncodeAST)
import qualified LLVM.Internal.FFI.DataLayout as L (getTypeAllocSize)
import qualified LLVM.IRBuilder.Instruction as L
import qualified LLVM.IRBuilder.Module as L
import qualified LLVM.IRBuilder.Monad as L
import GHC.Word (Word32, Word64)

sizeOf _ ctx (LLTT.Constant (LLTT.Local v _)) =
  Prelude.lookup v ctx
sizeOf env ctx (LLTT.Constant (LLTT.TypeCons v _)) = do
  def <- Env.lookup v env
  case def of
    LLTT.TypeDef _ equations _ -> do
      foldlM
        (\acc (_, _, tys) -> do
          size <- (+) 4 <$> foldlM (\acc ty -> (+) acc <$> sizeOf env ctx ty) 0 tys
          return $ max acc size
        )
        0
        equations
sizeOf _ _ (LLTT.Type _) =
  Just 4
sizeOf _ _ (LLTT.BytesType n) = do
  Just n
sizeOf env ctx (LLTT.Call (LLTT.TypeCons v _) args) = do
  args' <- mapM (sizeOf env ctx) args
  def <- Env.lookup v env
  case def of
    LLTT.TypeDef _ _ _ ->
      case Prelude.lookup v ctx of
        _ -> undefined
sizeOf env ctx (LLTT.Call (LLTT.TypeCons v _) args) = do
  def <- Env.lookup v env
  args' <- mapM (sizeOf env ctx) args
  case def of
    LLTT.TypeDef _ equations _ -> do
      foldlM
        (\acc (binds, _, tys) -> do
          let ctx' = zipWith (\(v, _) x -> (v, x)) binds args'  -- WRONG
          size <- foldlM (\acc ty -> (+) acc <$> sizeOf env ctx' ty) 0 tys
          return $ max acc size
        )
        0
        equations
sizeOf _ _ _ =
  Nothing

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

patGen
  :: (L.MonadModuleBuilder m, L.MonadIRBuilder m, MonadFix m)
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
  tagPtr <- L.bitcast op $ L.ptr $ L.IntegerType 32
  tagOp <- L.load tagPtr 0
  b <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral tag) tagOp
  return (b, [])
patGen env p@(Ann.PatApp _ _) op = case Ann.flattenPatApp p of
  Ann.Constructor consName : args -> do
    case Env.lookup consName env of
      Just (LLTT.ConstructorDef _ ty tag) -> do
        tagPtr <- L.bitcast op $ L.ptr $ L.i32
        tagOp <- L.load tagPtr 0
        b1 <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral tag) tagOp
        op' <- L.gep op [L.ConstantOperand $ L.Int 32 4]
        (b2, binds) <- deconstruct ty args op' []
        b <- L.and b1 b2
        return (b, binds)
      _ -> error ""
  _ -> error ""
  where
    deconstruct (LLTT.Pi v ty1 ty2) (arg:args) op ctx = do
      size <- codeGen env ctx ty1
      op' <- L.gep op [size]
      op'' <- loadIfSized env op ty1
      (b1, binds1) <- patGen env arg op''
      (b2, binds2) <- deconstruct ty2 args op' ((v, op'') : ctx)
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
      args' = map (typeGen env) args
      retTy' = typeGen env retTy
  function
    name
    args'
    retTy'
    (void $ genEquations args equations)
  return ()
  where
    genEquations
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [LLTT.Type]
      -> [([(String, LLTT.Type)], [Ann.Pattern], LLTT.Term)]
      -> L.IRBuilderT m L.Name
    genEquations _ [] =
      L.block <* L.unreachable
    genEquations args ((_, patterns, body):es) = mdo
      lb <- genEquation args patterns body lb'
      lb' <- genEquations args es
      return lb

    genEquation
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [LLTT.Type]
      -> [Ann.Pattern]
      -> LLTT.Term
      -> L.Name
      -> L.IRBuilderT m L.Name
    genEquation args patterns body lb = mdo
      n <- L.block
      args' <-
        zipWithM
          (\i ty ->
            let ty' = typeGen env ty
            in case sizeOf env [] ty of
              Nothing ->
                return $ L.LocalReference ty' $ L.UnName i
              Just n -> do
                ptr <- L.alloca ty' Nothing 0
                L.store ptr 0 $ L.LocalReference ty' $ L.UnName i
                L.bitcast ptr $ L.ptr $ L.i8
          )
          [0..]
          args
      xs <-
        zipWithM
          (patGen env)
          patterns
          args'
          {-
          (zipWith
            (\i argTy -> L.LocalReference argTy $ L.UnName i)
            [0..]
            args'
          )
          -}
      b <- foldlM L.and (L.ConstantOperand (L.Int 1 1)) (map fst xs)
      L.condBr b lb' lb
      lb' <- L.block
      let boundArgs = foldl (++) [] (map snd xs)
      L.ret =<< codeGen env boundArgs body
      return n
defGen env (LLTT.TypeDef name equations ty) = do
  let (args, retTy) = LLTT.flattenPi ty
      args' = map (typeGen env) args
      retTy' = typeGen env retTy
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
            x' <- codeGen env boundArgs x
            L.add x' acc
          )
          (L.ConstantOperand $ L.Int 32 4)
          body
      L.ret body'
      return n
defGen _ (LLTT.ConstructorDef _ _ _) = do
  return ()

construct1 env ctx (LLTT.Pi v ty1 ty2) (arg:args) = do
  construct1 env ((v, arg) : ctx) ty2 args
construct1 env ctx ty _ = do
  codeGen env ctx ty

construct2 env ctx (LLTT.Pi v ty1 ty2) op (arg:args) = do
  size <- codeGen env ctx ty1
  opPtr <- L.bitcast op $ L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
  argPtr <- L.bitcast arg $ L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
  _ <- L.call
    ( L.ConstantOperand
    $ L.GlobalReference
        (L.FunctionType
          L.VoidType
          [ L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
          , L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
          , L.IntegerType 32
          , L.IntegerType 1
          ]
          False
        )
        (L.mkName "llvm.memcpy.p0i8.p0i8.i32")
    )
    [(opPtr, []), (argPtr, []), (size, []), (L.ConstantOperand $ L.Int 1 1, [])]
  op' <- L.gep op [size]
  op'' <- loadIfSized env op ty1
  construct2 env ((v, op'') : ctx) ty2 op' args
construct2 env ctx ty _ [] =
  return ()

{-
loadIfSized
  :: L.MonadIRBuilder m
  => LLTT.Env
  -> L.Operand
  -> LLTT.Type
  -> m L.Operand
  -}
loadIfSized env op ty
  | Just _ <- sizeOf env [] ty = do
      let ty' = typeGen env ty
      op' <- L.bitcast op $ L.ptr ty'
      L.load op' 0
  | otherwise = do
      return op
  {-
loadIfSized env op ty
  | isSized ty = do
      let ty' = typeGen env ty
      op' <- L.bitcast op $ L.PointerType ty' $ L.AddrSpace 0
      L.load op' 0
  | otherwise = do
      return op
      -}

codeGen
  :: (L.MonadModuleBuilder m, L.MonadIRBuilder m, MonadFix m)
  => LLTT.Env
  -> [(String, L.Operand)]
  -> LLTT.Term
  -> m L.Operand
codeGen env ctx (LLTT.Constant (LLTT.Local v ty)) = do
  case snd <$> find ((==) v . fst) ctx of
    Just op ->
      return op
    Nothing -> do
      let ty' = typeGen env ty
      return $ L.LocalReference ty' $ L.mkName v
codeGen env _ (LLTT.Constant (LLTT.Global v ty)) = do
  let ty' = typeGen env ty
  L.load
    ( L.ConstantOperand
    $ L.GlobalReference (L.PointerType ty' $ L.AddrSpace 0)
    $ L.mkName v
    )
    0
codeGen env _ (LLTT.Constant (LLTT.TypeCons v ty)) = do
  let ty' = typeGen env ty
  L.call
    (L.ConstantOperand $ L.GlobalReference (L.FunctionType ty' [] False) $ L.mkName v)
    []
codeGen _ _ (LLTT.Num n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env ctx (LLTT.Call (LLTT.TypeCons v ty) args) =
  codeGen env ctx $ LLTT.Call (LLTT.Global v ty) args
codeGen env ctx (LLTT.Constant (LLTT.Constructor v ty)) =
  codeGen env ctx $ LLTT.Call (LLTT.Constructor v ty) []
codeGen env ctx (LLTT.Call (LLTT.Constructor v _) args) =
  case Env.lookup v env of
    Just (LLTT.ConstructorDef _ ty tag) -> mdo
      args' <- mapM (codeGen env ctx) args
      size <- construct1 env ctx ty args'
      op <- L.alloca (L.IntegerType 8) (Just size) 0
      tagPtr <- L.bitcast op $ L.PointerType (L.IntegerType 32) (L.AddrSpace 0)
      _ <- L.store tagPtr 0 $ L.ConstantOperand $ L.Int 32 $ fromIntegral tag
      op' <- L.gep op [L.ConstantOperand $ L.Int 32 4]
      construct2 env ctx ty op' args'
      return op
    _ ->
      error ""
codeGen env ctx (LLTT.Call (LLTT.Global v ty) args) = do
  let ty' = typeGen env ty
  L.call
    (L.ConstantOperand $ L.GlobalReference ty' $ L.mkName v)
    =<< mapM (fmap (flip (,) []) . codeGen env ctx) args
codeGen _ _ (LLTT.Call _ _) = do
  error ""
codeGen env ctx (LLTT.BinOp op a b) = do
  let instr = case op of
        TT.Add -> L.add
        TT.Sub -> L.sub
        TT.Mul -> L.mul
        _ -> undefined
  a' <- codeGen env ctx a
  b' <- codeGen env ctx b
  instr a' b'
codeGen _ _ (LLTT.UnOp _ _) = do
  undefined
codeGen _ _ (LLTT.BytesType n) = do
  return $ L.ConstantOperand $ L.Int 32 $ fromIntegral n
codeGen _ _ (LLTT.Type _) = do
  return $ L.ConstantOperand $ L.Int 32 4
codeGen _ _ t =
  error $ show t

typeGen :: LLTT.Env -> LLTT.Type -> L.Type
typeGen env ty@(LLTT.Pi _ _ _) =
  let (args, ret) = LLTT.flattenPi ty
  in L.FunctionType (typeGen env ret) (map (typeGen env) args) False
typeGen env (LLTT.BytesType n) =
  L.IntegerType $ fromIntegral (n*8)
typeGen env (LLTT.Type _) =
  L.IntegerType 32
typeGen env ty =
  case sizeOf env [] ty of
    Just n ->
      L.ArrayType (fromIntegral n) L.i8
    Nothing ->
      L.ptr L.i8
{-
typeGen env (LLTT.Constant _) =
  L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
typeGen env (LLTT.Constant (LLTT.TypeCons v _)) =
  --L.ArrayType undefined L.i8
  L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
typeGen env (LLTT.Call v _) =
  typeGen env $ LLTT.Constant v
  --L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
typeGen env t =
  error $ show t
-}

isSized :: LLTT.Type -> Bool
isSized (LLTT.Constant (LLTT.Local _ _)) =
  False
isSized (LLTT.Pi _ _ _) =
  undefined  -- lambdas are not yet implemented
isSized (LLTT.Constant _) =
  True
isSized (LLTT.Call v args) =
  isSized (LLTT.Constant v) && all isSized args
isSized _ =
  True
