{-# LANGUAGE RecursiveDo, FlexibleContexts #-}

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

match :: LLTT.Pattern -> LLTT.Term -> Maybe [(String, LLTT.Term)]
match (Ann.Binding n _) t =
  Just [(n, t)]
match (Ann.Inaccessible _) _ =
  Just []
match (Ann.NumPat n _) (LLTT.Num n' _) =
  if n == n' then
    Just []
  else
    Nothing
match (Ann.NumPat _ _) _ =
  Nothing
match p'@(Ann.NumSucc p) (LLTT.BinOp TT.Add x y) =
  case (simplify x, simplify y) of
    (_, LLTT.Num 0 _) ->
      match p' x
    (LLTT.Num 0 _, _) ->
      match p' y
    (_, LLTT.Num n b) ->
      match p $ simplify $ LLTT.BinOp TT.Add x (LLTT.Num (n-1) b)
    (LLTT.Num n b, _) ->
      match p $ simplify $ LLTT.BinOp TT.Add (LLTT.Num (n-1) b) y
    _ ->
      Nothing
match (Ann.NumSucc p) x | LLTT.Num n b <- simplify x =
  match p $ LLTT.Num (n-1) b
match (Ann.NumSucc _) _ =
  Nothing
match (Ann.Constructor n) (LLTT.Constant (LLTT.Constructor n' _)) =
  if n == n' then
    Just []
  else
    Nothing
match (Ann.Constructor _) _ =
  Nothing
match p@(Ann.PatApp _ _) (LLTT.Call v args _) =
  case Ann.flattenPatApp p of
    hd : tl -> do
      l <- match hd $ LLTT.Constant v
      l' <- concat <$> zipWithM match tl args
      return (l ++ l')
    _ ->
      Nothing
match (Ann.PatApp _ _) _ =
  Nothing

simplify :: LLTT.Term -> LLTT.Term
simplify (LLTT.BinOp TT.Add (LLTT.Num x b) (LLTT.Num y b')) | b == b' =
  LLTT.Num (x+y) b
simplify (LLTT.BinOp TT.Add x@(LLTT.Num _ _) y) =
  simplify (LLTT.BinOp TT.Add y x)
simplify (LLTT.BinOp TT.Add x (LLTT.Num 0 _)) =
  simplify x
simplify v =
  v

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
sizeOf _ _ LLTT.ErasedType =
  Just 0
sizeOf _ _ (LLTT.BytesType n) = do
  Just n
sizeOf env ctx (LLTT.Call (LLTT.TypeCons v _) args _) = do
  def <- Env.lookup v env
  args' <- mapM (sizeOf env ctx) args
  case def of
    LLTT.TypeDef _ equations _ -> do
      foldlM
        (\acc (binds, pats, tys) -> do
          case concat <$> zipWithM match pats args of
            Just ctx'' -> do
              ctx' <- mapM (\(v, ty) -> do ty' <- sizeOf env [] ty; return (v, ty')) ctx''
              size <- foldlM (\acc' ty -> (+) acc' <$> sizeOf env ctx' ty) 4 tys
              return $ max acc size
            Nothing ->
              return acc
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

succPatGen env ctx (Ann.NumSucc p) op i =
  succPatGen env ctx p op (i+1)
succPatGen env ctx (Ann.Binding x ty@(LLTT.BytesType b)) op i = do
  op' <- loadIfSized env ctx op ty
  op'' <- L.sub op'
            $ L.ConstantOperand $ L.Int (fromIntegral (b*8)) (fromIntegral i)
  bl <- L.icmp L.SGE op'' $ L.ConstantOperand $ L.Int (fromIntegral (b*8)) 0
  return (bl, [(x, op'')])

patGen
  :: ( L.MonadModuleBuilder m, L.MonadIRBuilder m, MonadFix m, MonadExcept m
     , MonadLog m
     )
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
patGen env ctx p@(Ann.NumSucc _) op = do
  succPatGen env ctx p op 0
patGen env _ (Ann.Constructor consName) op = do
  tag <- case Env.lookup consName env of
        Just (LLTT.ConstructorDef _ _ tag') ->
          return tag'
        _ ->
          throwError "patGen Ann.Constructor"
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
      _ -> throwError "patGen Ann.PatApp"
  _ -> do
    return (L.ConstantOperand $ L.Int 1 1, [])
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
  :: (L.MonadModuleBuilder m, MonadFix m, MonadLog m, MonadExcept m)
  => LLTT.Env
  -> LLTT.Def
  -> m ()
defGen env (LLTT.PatternMatchingDef name equations ty) = do
  tell ("defGen " ++ name)
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
      :: (L.MonadModuleBuilder m, MonadFix m, L.MonadIRBuilder m, MonadExcept m
         , MonadLog m
         )
      => [LLTT.Type]
      -> LLTT.Type
      -> [([(String, LLTT.Type)], [LLTT.Pattern], LLTT.Term)]
      -> m L.Name
    genEquations _ _ [] =
      L.block <* L.unreachable
    genEquations args retTy ((_, patterns, body):es) = mdo
      lb <- genEquation args retTy patterns body lb'
      lb' <- genEquations args retTy es
      return lb

    genEquation
      :: (L.MonadModuleBuilder m, MonadFix m, L.MonadIRBuilder m, MonadExcept m
         , MonadLog m
         )
      => [LLTT.Type]
      -> LLTT.Type
      -> [LLTT.Pattern]
      -> LLTT.Term
      -> L.Name
      -> m L.Name
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
  tell ("defGen " ++ name)
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
      :: (L.MonadModuleBuilder m, MonadFix m, L.MonadIRBuilder m, MonadExcept m
         , MonadLog m
         )
      => [LLTT.Type]
      -> [([(String, LLTT.Type)], [LLTT.Pattern], [LLTT.Type])]
      -> m L.Name
    genEquations _ [] =
      L.block <* L.unreachable
    genEquations args ((_, patterns, body):es) = mdo
      lb <- genEquation args patterns body lb'
      lb' <- genEquations args es
      return lb

    genEquation
      :: ( L.MonadModuleBuilder m, MonadFix m, L.MonadIRBuilder m, MonadExcept m
         , MonadLog m
         )
      => [LLTT.Type]
      -> [LLTT.Pattern]
      -> [LLTT.Type]
      -> L.Name
      -> m L.Name
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
  tell ("defGen " ++ name)
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
defGen env (LLTT.ExternDef name ty) = do
  {-
  let
    (args, retTy) = LLTT.flattenPi ty
    args' = map (typeGen env) args
    retTy' = typeGen env retTy
  _ <- L.function
    (L.mkName name)
    (map (flip (,) L.NoParameterName) args')
    retTy'
    (const $ return ())
  -}
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
  :: ( L.MonadModuleBuilder m, L.MonadIRBuilder m, MonadFix m, MonadExcept m
     , MonadLog m
     )
  => LLTT.Env
  -> [(String, L.Operand)]
  -> [(String, Int)]
  -> LLTT.Term
  -> m L.Operand
codeGen env ctx sizeCtx (LLTT.Constant (LLTT.Local v ty)) = do
  tell ("codeGen LLTT.Constant: " ++ show (LLTT.Constant (LLTT.Local v ty)))
  case snd <$> find ((==) v . fst) ctx of
    Just op ->
      return op
    Nothing -> do
      throwError ("codeGen LLTT.Constant: " ++ v)
codeGen env _ sizeCtx (LLTT.Constant (LLTT.Global v ty)) = do
  tell "codeGen env _ sizeCtx (LLTT.Constant (LLTT.Global v ty))"
  let ty' = typeGen env ty
  L.call
    ( L.ConstantOperand
    $ L.GlobalReference (L.FunctionType ty' [] False)
    $ L.mkName v
    )
    []
codeGen env ctx sizeCtx (LLTT.Constant (LLTT.TypeCons v ty)) = do
  tell "codeGen env ctx sizeCtx (LLTT.Constant (LLTT.TypeCons v ty))"
  codeGen env ctx sizeCtx (LLTT.Constant (LLTT.Global v ty))
codeGen _ _ _ (LLTT.Num n bytes') = do
  tell ("codeGen LLTT.Num: " ++ show (LLTT.Num n bytes'))
  return (L.ConstantOperand (L.Int (fromIntegral bytes' * 8) (fromIntegral n)))
codeGen env ctx sizeCtx (LLTT.Call (LLTT.TypeCons v ty) args ty') = do
  tell ("codeGen LLTT.Call: " ++ show (LLTT.Call (LLTT.TypeCons v ty) args ty'))
  codeGen env ctx sizeCtx $ LLTT.Call (LLTT.Global v ty) args ty'
codeGen env ctx sizeCtx (LLTT.Constant (LLTT.Constructor v ty)) = do
  tell "codeGen env ctx sizeCtx (LLTT.Constant (LLTT.Constructor v ty))"
  codeGen env ctx sizeCtx $ LLTT.Call (LLTT.Constructor v ty) [] ty
codeGen env ctx sizeCtx t@(LLTT.Call (LLTT.Constructor v ty) args ty') = do
  tell "codeGen env ctx sizeCtx t@(LLTT.Call (LLTT.Constructor v ty) args ty')"
  codeGen env ctx sizeCtx $ LLTT.Call (LLTT.Global v ty) args ty'
codeGen env ctx sizeCtx (LLTT.Call (LLTT.Global v ty) [] ty'') = do
  tell ("codeGen LLTT.Call: " ++ show (LLTT.Call (LLTT.Global v ty) [] ty''))
  let ty' = typeGen env ty
  L.call
    ( L.ConstantOperand
    $ L.GlobalReference (L.FunctionType ty' [] False)
    $ L.mkName v)
    []
codeGen env ctx sizeCtx (LLTT.Call (LLTT.Global v ty) args ty'') = do
  tell ("codeGen LLTT.Call: " ++ show (LLTT.Call (LLTT.Global v ty) args ty''))
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
  tell "codeGen _ _ _ (LLTT.Call _ _ _)"
  throwError "codeGen LLTT.Call"
codeGen env ctx sizeCtx (LLTT.BinOp op a b) = do
  tell "codeGen env ctx sizeCtx (LLTT.BinOp op a b)"
  let instr = case op of
        TT.Add -> L.add
        TT.Sub -> L.sub
        TT.Mul -> L.mul
        _ -> undefined
  a' <- codeGen env ctx sizeCtx a
  b' <- codeGen env ctx sizeCtx b
  instr a' b'
codeGen _ _ _ (LLTT.UnOp _ _) = do
  tell "codeGen _ _ _ (LLTT.UnOp _ _)"
  undefined
codeGen _ _ _ (LLTT.BytesType n) = do
  tell ("codeGen LLTT.BytesType: " ++ show (LLTT.BytesType n))
  return $ L.ConstantOperand $ L.Int 32 $ fromIntegral n
codeGen _ _ _ LLTT.Type = do
  tell "codeGen _ _ _ LLTT.Type"
  return $ L.ConstantOperand $ L.Int 32 4
codeGen _ ctx _ LLTT.ErasedType = do
  tell "codeGen _ ctx _ LLTT.ErasedType"
  return $ L.ConstantOperand $ L.Int 32 0
codeGen _ ctx _ LLTT.ErasedTerm = do
  tell "codeGen _ ctx _ LLTT.ErasedTerm"
  --L.alloca L.i8 (Just $ L.ConstantOperand $ L.Int 32 0) 0
  return $ L.ConstantOperand $ L.Array L.i8 []
codeGen _ ctx _ t = do
  tell "codeGen _ ctx _ t"
  throwError ("codeGen t: " ++ show t ++ "; " ++ show ctx)

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
