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
import Data.Maybe (fromJust, isJust)
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
sizeOf _ _ LLTT.Type =
  Just 4
sizeOf _ _ (LLTT.BytesType n) = do
  Just n
sizeOf env ctx (LLTT.Call (LLTT.TypeCons v _) args _) = do
  def <- Env.lookup v env
  args' <- mapM (sizeOf env ctx) args
  case def of
    LLTT.TypeDef _ equations _ -> do
      foldlM
        (\acc (binds, _, tys) -> do
          let ctx' = zipWith (\(v, _) x -> (v, x)) binds args'  -- WRONG
          size <- foldlM (\acc ty -> (+) acc <$> sizeOf env ctx' ty) 4 tys
          return $ max acc size
        )
        0
        equations
sizeOf _ _ _ =
  Nothing

isSized env ctx ty =
  isJust $ sizeOf env ctx ty

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
  -> [(String, Int)]
  -> LLTT.Pattern
  -> L.Operand
  -> m (L.Operand, [(String, L.Operand)])
patGen env ctx (Ann.Binding x ty) op = do
  op' <- loadIfSized env ctx op ty
  return (L.ConstantOperand (L.Int 1 1), [(x, op')])
patGen _ _ (Ann.Inaccessible _) _ =
  return (L.ConstantOperand (L.Int 1 1), [])
patGen env ctx (Ann.NumPat n b) op = do
  op' <- loadIfSized env ctx op (LLTT.BytesType b)
  x <-
    L.icmp
      L.EQ
      (L.ConstantOperand (L.Int (fromIntegral (b*8)) (fromIntegral n)))
      op'
  return (x, [])
patGen env _ (Ann.Constructor consName) op = do
  let tag = case Env.lookup consName env of
        Just (LLTT.ConstructorDef _ _ tag') ->
          tag'
        _ ->
          error ""
  tagPtr <- L.bitcast op $ L.ptr $ L.IntegerType 32
  tagOp <- L.load tagPtr 0
  b <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral tag) tagOp
  return (b, [])
patGen env sizeCtx p@(Ann.PatApp _ _) op = case Ann.flattenPatApp p of
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
      size <- codeGen env ctx sizeCtx ty1
      op' <- L.gep op [size]
      (b1, binds1) <- patGen env sizeCtx arg op
      op'' <- loadIfSized env sizeCtx op ty1
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
  function
    name
    (if directCall then args' else args' ++ [L.ptr L.i8])
    (if directCall then retTy' else L.void)
    (void $ genEquations args retTy equations)
  return ()
  where
    (args, retTy) = LLTT.flattenPi ty
    args' = map (typeGen env) args
    retTy' = typeGen env retTy
    directCall = isSized env [] retTy

    retTySize ctx i (LLTT.Pi v ty1 ty2) = do
      let ty' = typeGen env ty1
      retTySize ((v, L.LocalReference ty' $ L.UnName i) : ctx) (i+1) ty2
    retTySize ctx i _ = do
      codeGen env ctx [] retTy

    genEquations
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [LLTT.Type]
      -> LLTT.Type
      -> [([(String, LLTT.Type)], [LLTT.Pattern], LLTT.Term)]
      -> L.IRBuilderT m L.Name
    genEquations _ _ [] =
      L.block <* L.unreachable
    genEquations args retTy ((_, patterns, body):es) = mdo
      lb <- genEquation args retTy patterns body lb'
      lb' <- genEquations args retTy es
      return lb

    genEquation
      :: (L.MonadModuleBuilder m, MonadFix m)
      => [LLTT.Type]
      -> LLTT.Type
      -> [LLTT.Pattern]
      -> LLTT.Term
      -> L.Name
      -> L.IRBuilderT m L.Name
    genEquation args retTy patterns body lb = mdo
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
                L.bitcast ptr $ L.ptr L.i8
          )
          [0..]
          args
      xs <- zipWithM (patGen env []) patterns args'
      b <- foldlM L.and (L.ConstantOperand (L.Int 1 1)) (map fst xs)
      L.condBr b lb' lb
      lb' <- L.block
      let boundArgs = foldl (++) [] (map snd xs)
      ret =<< codeGen env boundArgs [] body
      return n
    ret op
      | directCall =
          L.ret op
      | otherwise = do
          memcpy
            (L.LocalReference retTy' $ L.UnName $ fromIntegral $ length args')
            op
            =<< retTySize [] 0 ty
          L.retVoid
defGen env (LLTT.TypeDef name equations ty) = do
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
      -> [([(String, LLTT.Type)], [LLTT.Pattern], [LLTT.Type])]
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
      -> [LLTT.Pattern]
      -> [LLTT.Type]
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
                --return $ L.LocalReference ty' $ L.UnName i
                ptr <- L.alloca ty' Nothing 0
                L.store ptr 0 $ L.LocalReference ty' $ L.UnName i
                L.bitcast ptr $ L.ptr $ L.i8
          )
          [0..]
          args
      xs <- zipWithM (patGen env []) patterns args'
      b <- foldlM L.and (L.ConstantOperand (L.Int 1 1)) (map fst xs)
      L.condBr b lb' lb
      lb' <- L.block
      let boundArgs = foldl (++) [] (map snd xs)
      body' <- foldlM (\acc x -> do
            x' <- codeGen env boundArgs [] x
            L.add x' acc
          )
          (L.ConstantOperand $ L.Int 32 4)
          body
      L.ret body'
      return n
defGen env (LLTT.ConstructorDef name ty tag) = do
  let (args, retTy) = LLTT.flattenPi ty
      args' = map (typeGen env) args
      retTy' = typeGen env retTy
      directCall = isSized env [] retTy
  _ <- L.function
    (L.mkName name)
    (map (flip (,) L.NoParameterName) args' ++ if directCall then [] else [(L.ptr L.i8, L.NoParameterName)])
    (if directCall then retTy' else L.void)
    (\asdf -> do
      let args = (if directCall then id else init) asdf
      size <- construct1 env [] [] ty args
      op <- L.alloca L.i8 (Just size) 0
      tagPtr <- L.bitcast op $ L.ptr L.i32
      _ <- L.store tagPtr 0 $ L.ConstantOperand $ L.Int 32 $ fromIntegral tag
      op' <- L.gep op [L.ConstantOperand $ L.Int 32 4]
      construct2 env [] [] ty op' args
      if directCall then
        L.ret =<< loadIfSized env [] op retTy
      else do
        let
          retTySize ctx i (LLTT.Pi v ty1 ty2) = do
            let ty' = typeGen env ty1
            retTySize ((v, L.LocalReference ty' $ L.UnName i) : ctx) (i+1) ty2
          retTySize ctx i ty = do
            codeGen env ctx [] ty

        memcpy
          (L.LocalReference retTy' $ L.UnName $ fromIntegral $ length args)
          op
          =<< retTySize [] 0 ty
        L.retVoid
    )
  return ()

construct1 env ctx sizeCtx (LLTT.Pi v ty1 ty2) (arg:args) = do
  construct1 env ((v, arg) : ctx) sizeCtx ty2 args
construct1 env ctx sizeCtx ty _ = do
  codeGen env ctx sizeCtx ty

memcpy dest orig size =
  void $ L.call
    ( L.ConstantOperand
    $ L.GlobalReference
        (L.FunctionType L.void [ L.ptr L.i8, L.ptr L.i8, L.i32, L.i1 ] False)
        (L.mkName "llvm.memcpy.p0i8.p0i8.i32")
    )
    [(dest, []), (orig, []), (size, []), (L.ConstantOperand $ L.Int 1 0, [])]

fnType env directCall ty =
  if directCall then
    typeGen env ty
  else
    let (args, retTy) = LLTT.flattenPi ty
    in L.FunctionType L.void (map (typeGen env) args ++ [L.ptr L.i8]) False

construct2 env ctx sizeCtx (LLTT.Pi v ty1 ty2) op (arg:args) = do
  size <- codeGen env ctx sizeCtx ty1
  opPtr <- L.bitcast op $ L.ptr L.i8
  arg_ <- allocaIfSized env sizeCtx arg ty1
  argPtr <- L.bitcast arg_ $ L.ptr L.i8
  memcpy opPtr argPtr size
  op' <- L.gep op [size]
  op'' <- loadIfSized env sizeCtx op ty1
  construct2 env ((v, op'') : ctx) sizeCtx ty2 op' args
construct2 _ _ _ _ _ [] =
  return ()

loadIfSized, allocaIfSized
  :: L.MonadIRBuilder m
  => LLTT.Env
  -> [(String, Int)]
  -> L.Operand
  -> LLTT.Type
  -> m L.Operand
loadIfSized env ctx op ty
  | Just _ <- sizeOf env ctx ty = do
      let ty' = typeGen env ty
      op' <- L.bitcast op $ L.ptr ty'
      L.load op' 1
  | otherwise = do
      return op

allocaIfSized env ctx op ty
  | Just _ <- sizeOf env ctx ty = do
      let ty' = typeGen env ty
      ptr <- L.alloca ty' Nothing 0
      L.store ptr 0 op
      return ptr
  | otherwise = do
      return op

codeGen
  :: (L.MonadModuleBuilder m, L.MonadIRBuilder m, MonadFix m)
  => LLTT.Env
  -> [(String, L.Operand)]
  -> [(String, Int)]
  -> LLTT.Term
  -> m L.Operand
codeGen env ctx sizeCtx (LLTT.Constant (LLTT.Local v ty)) = do
  case snd <$> find ((==) v . fst) ctx of
    Just op ->
      --loadIfSized env op ty
      return op
    Nothing -> do
      error (v ++ " : " ++ show ty ++ "; " ++ show ctx)
      let ty' = typeGen env ty
          op = L.LocalReference ty' $ L.mkName v
      --loadIfSized env op ty
      return op
codeGen env _ sizeCtx (LLTT.Constant (LLTT.Global v ty)) = do
  let ty' = typeGen env ty
  L.load
    ( L.ConstantOperand
    $ L.GlobalReference (L.PointerType ty' $ L.AddrSpace 0)
    $ L.mkName v
    )
    0
codeGen env _ sizeCtx (LLTT.Constant (LLTT.TypeCons v ty)) = do
  let ty' = typeGen env ty
  L.call
    (L.ConstantOperand $ L.GlobalReference (L.FunctionType ty' [] False) $ L.mkName v)
    []
codeGen _ _ _ (LLTT.Num n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env ctx sizeCtx (LLTT.Call (LLTT.TypeCons v ty) args ty') =
  codeGen env ctx sizeCtx $ LLTT.Call (LLTT.Global v ty) args ty'
codeGen env ctx sizeCtx (LLTT.Constant (LLTT.Constructor v ty)) =
  codeGen env ctx sizeCtx $ LLTT.Call (LLTT.Constructor v ty) [] ty
codeGen env ctx sizeCtx t@(LLTT.Call (LLTT.Constructor v ty) args ty') =
  codeGen env ctx sizeCtx $ LLTT.Call (LLTT.Global v ty) args ty'
codeGen env ctx sizeCtx (LLTT.Call (LLTT.Global v ty) [] ty'') = do
  let ty' = typeGen env ty
  L.call
    ( L.ConstantOperand
    $ L.GlobalReference (L.FunctionType ty' [] False)
    $ L.mkName v)
    []
codeGen env ctx sizeCtx (LLTT.Call (LLTT.Global v ty) args ty'') = do
  let directCall = isSized env sizeCtx retTy
      ty' = fnType env directCall ty
      (_, retTy) = LLTT.flattenPi ty
  args' <- map (flip (,) []) <$> f args ty
  let v' = L.ConstantOperand $ L.GlobalReference ty' $ L.mkName v
  if directCall then
    L.call v' args'
  else do
    size <- codeGen env ctx sizeCtx ty''
    op <- L.alloca L.i8 (Just size) 0
    L.call v' (args' ++ [(op, [])])
    loadIfSized env sizeCtx op ty''
  where
    f [] _ =
      return []
    f (a:as) (LLTT.Pi v ty1 ty2) = do
      a' <- codeGen env ctx sizeCtx a
      if isSized env sizeCtx ty1 then do
        as' <- f as ty2
        return (a' : as')
      else do
        a'' <- allocaIfSized env sizeCtx a' $ LLTT.typeInf a
        a''' <- L.bitcast a'' $ L.ptr L.i8
        as' <- f as ty2
        return (a''' : as')
codeGen _ _ _ (LLTT.Call _ _ _) = do
  error ""
codeGen env ctx sizeCtx (LLTT.BinOp op a b) = do
  let instr = case op of
        TT.Add -> L.add
        TT.Sub -> L.sub
        TT.Mul -> L.mul
        _ -> undefined
  a' <- codeGen env ctx sizeCtx a
  b' <- codeGen env ctx sizeCtx b
  instr a' b'
codeGen _ _ _ (LLTT.UnOp _ _) = do
  undefined
codeGen _ _ _ (LLTT.BytesType n) = do
  return $ L.ConstantOperand $ L.Int 32 $ fromIntegral n
codeGen _ _ _ LLTT.Type = do
  return $ L.ConstantOperand $ L.Int 32 4
codeGen _ ctx _ t =
  error (show t ++ "; " ++ show ctx)

typeGen :: LLTT.Env -> LLTT.Type -> L.Type
typeGen env ty@(LLTT.Pi _ _ _) =
  let (args, ret) = LLTT.flattenPi ty
  in L.FunctionType (typeGen env ret) (map (typeGen env) args) False
typeGen _ (LLTT.BytesType n) =
  L.IntegerType $ fromIntegral (n*8)
typeGen _ LLTT.Type =
  L.IntegerType 32
typeGen env ty =
  case sizeOf env [] ty of
    Just n ->
      L.ArrayType (fromIntegral n) L.i8
    Nothing ->
      L.ptr L.i8
