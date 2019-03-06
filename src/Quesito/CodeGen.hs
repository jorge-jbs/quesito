{-# LANGUAGE RecursiveDo, FlexibleContexts, LambdaCase #-}

module Quesito.CodeGen where

import Prelude hiding (lookup)
import qualified Prelude

import Quesito.CodeGen.TopLevel
import qualified Quesito.Ann as Ann
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
import qualified LLVM.IRBuilder.Monad as L
import GHC.Word (Word32, Word64)

getSize
  :: MonadCodeGen m
  => Ann.Type
  -> L.Operand
  -> [(String, L.Operand)]
  -> L.IRBuilderT m L.Operand
getSize (Ann.BytesType n) _ _ =
  return $ L.ConstantOperand $ L.Int 32 $ fromIntegral n
getSize (Ann.Type _) op _ =
  return $ L.ConstantOperand $ L.Int 32 4  -- function pointer
getSize (Ann.Local v _) op env = do
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
getSize (Ann.Global v ty) op _ =
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
getSize (Ann.App t _) op env =
  getSize t op env
getSize _ _ _ =
  undefined

sizeOf :: L.Type -> IO Word64
sizeOf ty = L.withContext $ \ctx -> L.runEncodeAST ctx $ do
  ty' <- L.encodeM ty
  liftIO (L.withFFIDataLayout
    (L.defaultDataLayout L.LittleEndian)
    (\dl -> L.getTypeAllocSize dl ty'))


defGen :: MonadCodeGen m => Ann.Def -> m ()
defGen (Ann.PatternMatchingDef name equations ty _) = do
  let (args, retTy) = Ann.flattenPi ty
  args' <- mapM typeGen args
  retTy' <- typeGen retTy
  function
    name
    args'
    retTy'
    (void $ genEquations args' equations)
  return ()
  where
    genEquations :: MonadCodeGen m => [L.Type] -> [([(String, Ann.Type)], [Ann.Pattern], Ann.Term)] -> L.IRBuilderT m L.Name
    genEquations _ [] =
      L.block <* L.unreachable
    genEquations args' ((_, patterns, body):es) = mdo
      lb <- genEquation args' patterns body lb'
      lb' <- genEquations args' es
      return lb

    genEquation :: MonadCodeGen m => [L.Type] -> [Ann.Pattern] -> Ann.Term -> L.Name -> L.IRBuilderT m L.Name
    genEquation args' patterns body lb = mdo
      n <- L.block
      xs <-
        mapM
          (uncurry patGen)
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

    patGen :: MonadCodeGen m => Ann.Pattern -> L.Operand -> L.IRBuilderT m (L.Operand, [(String, L.Operand)])
    patGen (Ann.Binding x) op =
      return (L.ConstantOperand (L.Int 1 1), [(x, op)])
    patGen (Ann.Inaccessible _) _ =
      undefined
    patGen (Ann.NumPat n b) op = do
      x <- L.icmp L.EQ (L.ConstantOperand (L.Int (fromIntegral (b*8)) (fromIntegral n))) op
      return (x, [])
    patGen (Ann.Constructor consName) op = do
      def <- lift $ lookup consName
      let n = case def of
            Just (Constructor _ _ tag _) ->
              tag
            _ ->
              error ""
      m <- L.extractValue op [0]
      b <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral n) m
      return (b, [])
    patGen p@(Ann.PatApp _ _) op = case Ann.flattenPatApp p of
      Ann.Constructor consName : args -> do
        def <- lift $ lookup consName
        case def of
          Just (Constructor _ retTy _ (FunctionConstructor _ consTy)) -> do
            ptr <- L.alloca retTy Nothing 0
            L.store ptr 0 op
            ptr' <- L.bitcast
              ptr
              (L.PointerType
                (L.StructureType
                  False
                  [L.IntegerType 32, consTy]
                )
                (L.AddrSpace 0)
              )
            deptr <- L.load ptr' 0
            gen <- forM (zip [0..] args) (\(i, arg) -> do
                op' <- L.extractValue deptr [1, i]
                patGen arg op'
              )
            foldlM
              (\(b1, binds1) (b2, binds2) -> do
                b <- L.and b1 b2
                return (b, binds1 ++ binds2)
              )
              (L.ConstantOperand (L.Int 1 1), [])
              gen
          _ -> error ""
      _ -> error ""
defGen (Ann.TypeDef name _ cons) = do
  --let flattened = map (flatten . snd) cons
  --getConsLTypes <- mapM (getConsLType . fst) flattened
  --maxSize <- liftIO (maximum <$> mapM sizeOf getConsLTypes)
  typeDef
    name
    (\op -> mdo
      tagPtr <- L.bitcast op $ L.PointerType (L.IntegerType 32) (L.AddrSpace 0)
      tag <- L.load tagPtr 0
      L.br bl
      bl <- sizeCons cons op tag 0
      return ()
    )
    {-
    (L.StructureType
      False
      [L.IntegerType 32, L.ArrayType maxSize (L.IntegerType 8)]
    )
    -}
    --(fromIntegral maxSize)
        {-
  forM_ (zip4 [0..] getConsLTypes flattened (map fst cons)) (\(n, consLType, (args, retTy), consName) -> do
      retTy' <- typeGen retTy
      args' <- mapM typeGen args
      if length args == 0 then
        --emptyConstructor consName retTy' n maxSize
        return ()
      else
        functionConstructor consName args' consLType retTy' n
          (do
            z <- L.alloca consLType Nothing 0
            x <- constructor 0 args' consLType
            L.store z 0 x
            w <-
              L.bitcast z
               (L.PointerType
                 (L.ArrayType maxSize (L.IntegerType 8))
                 (L.AddrSpace 0)
               )
            y <-
              L.insertValue
                (L.ConstantOperand (L.Undef retTy'))
                (L.ConstantOperand (L.Int 32 n))
                [0]
            a <- L.load w 0
            L.ret =<< L.insertValue y a [1]
          )
          return ()
      return ()
    )
          -}
  return ()
  where
    flatten :: Ann.Type -> ([Ann.Type], Ann.Type)
    flatten (Ann.Pi _ arg t) =
      let (args, retTy) = flatten t
      in (arg : args, retTy)
    flatten t =
      ([], t)

    getConsLType :: MonadCodeGen m => [Ann.Type] -> m L.Type
    getConsLType tys =
      L.StructureType False <$> mapM typeGen tys

    constructor :: (MonadCodeGen m) => Word32 -> [L.Type] -> L.Type -> L.IRBuilderT m L.Operand
    constructor _ [] ty =
      return (L.ConstantOperand (L.Undef ty))
    constructor n (arg:args) ty = do
      x <- constructor (n+1) args ty
      L.insertValue x (L.LocalReference arg (L.UnName (fromIntegral $ toInteger n))) [n]

    sizeCons
      :: MonadCodeGen m
      => [(String, Ann.Type)]
      -> L.Operand
      -> L.Operand
      -> Int
      -> L.IRBuilderT m L.Name
    sizeCons [] _ _ _ =
      L.block <* L.unreachable
    sizeCons ((_, ty):conss') op tag n = mdo
      bll <- L.block
      b <- L.icmp L.EQ (L.ConstantOperand $ L.Int 32 $ fromIntegral n) tag
      L.condBr b bl bl'
      bl <- L.block
      op' <- L.gep op [L.ConstantOperand $ L.Int 32 4]
      L.ret =<< getSizeCons ty op' []
      bl' <- sizeCons conss' op tag (n+1)
      return bll

    getSizeCons
      :: MonadCodeGen m
      => Ann.Type
      -> L.Operand
      -> [(String, L.Operand)]
      -> L.IRBuilderT m L.Operand
    getSizeCons (Ann.Pi v ty1 ty2) op env = do
      size <- getSize ty1 op env
      op' <- L.gep op [size]
      size' <- getSizeCons ty2 op' ((v, op):env)
      L.add size size'
    getSizeCons _ _ _ =
      return $ L.ConstantOperand $ L.Int 32 4  -- function pointer

codeGen :: MonadCodeGen m => [(String, L.Operand)] -> Ann.Term -> L.IRBuilderT m L.Operand
codeGen env (Ann.Local v ty) =
  case snd <$> find ((==) v . fst) env of
    Just op ->
      return op
    Nothing -> do
      ty' <- lift $ typeGen ty
      return $ L.LocalReference ty' $ L.mkName v
codeGen _ (Ann.Global v ty) = do
  ty' <- lift $ typeGen ty
  L.load
    ( L.ConstantOperand
    $ L.GlobalReference (L.PointerType ty' $ L.AddrSpace 0)
    $ L.mkName v
    )
    0
codeGen _ (Ann.Num n bytes') =
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env t@(Ann.App _ _) = do
  case Ann.flattenApp t of
    Ann.Global v ty : args -> do
      ty' <- lift $ typeGen ty
      L.call
        (L.ConstantOperand $ L.GlobalReference ty' $ L.mkName v)
        =<< mapM (fmap (flip (,) []) . codeGen env) args
    [Ann.BinOp op, a, b] -> do
      let instr = case op of
            TT.Add -> L.add
            TT.Sub -> L.sub
            TT.Mul -> L.mul
            _ -> undefined
      a' <- codeGen env a
      b' <- codeGen env b
      instr a' b'
    [Ann.UnOp _, _] -> do
      undefined
    _ ->
      error (show t)
codeGen _ _ =
  undefined

typeGen :: MonadCodeGen m => Ann.Type -> m L.Type
typeGen ty@(Ann.Pi _ _ _) =
  let (args, ret) = Ann.flattenPi ty
  in L.FunctionType <$> typeGen ret <*> mapM typeGen args <*> pure False
typeGen (Ann.BytesType n) =
  return $ L.IntegerType $ fromIntegral (n*8)
typeGen (Ann.Type _) = do
  return
    $ flip L.PointerType (L.AddrSpace 0)
    $ L.FunctionType
        (L.IntegerType 32)
        [L.PointerType (L.IntegerType 8) (L.AddrSpace 0)]
        False
typeGen (Ann.Local x _) = do
  return $ L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
  --undefined
typeGen (Ann.Global x _) = do
  return $ L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
  {-
  def <- lookup x
  return (case def of
    Just (Type _ ty) ->
      ty
    _ ->
      error "")
      -}
typeGen t =
  error $ show t
