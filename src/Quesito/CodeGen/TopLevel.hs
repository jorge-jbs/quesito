{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Quesito.CodeGen.TopLevel where

import Prelude hiding (lookup)
import Control.Monad.State (StateT, MonadState, evalStateT, get, modify)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Fix (MonadFix)
import Data.Word (Word64)

import qualified LLVM.AST as L hiding (function)
import qualified LLVM.AST.Constant as L
import qualified LLVM.IRBuilder.Module as L
import qualified LLVM.IRBuilder.Monad as L

import qualified Quesito.Env as Env

data Constructor
  = EmptyConstructor
  | FunctionConstructor
      [L.Type]  -- ^ arguments types
      L.Type  -- ^ struct
  deriving Show

data Def
  = Function
      String  -- ^ name
      [L.Type]  -- ^ arguments types
      L.Type  -- ^ return type
  | Constructor
      String  -- ^ constructor name
      L.Type  -- ^ type name
      Integer  -- ^ tag
      Constructor
  | Type
      String  -- ^ name
      L.Type
  deriving Show

instance Env.Definition Def where
  getNames (Function n _ _) =
    [n]
  getNames (Constructor n _ _ _) =
    [n]
  getNames (Type n _) =
    [n]

class (MonadIO m, MonadFix m) => MonadCodeGen m where
  lookup :: String -> m (Maybe Def)
  function :: String -> [L.Type] -> L.Type -> L.IRBuilderT m () -> m ()
  typeDef :: String -> L.Type -> m ()
  functionConstructor
    :: String
    -> [L.Type]
    -> L.Type
    -> L.Type
    -> Integer
    -> L.IRBuilderT m ()
    -> m ()
  emptyConstructor :: String -> L.Type -> Integer -> Word64 -> m ()

type CodeGenState = Env.Env Def

newtype CodeGenM a = CodeGenM
  { unCodeGenM :: StateT CodeGenState (L.ModuleBuilderT IO) a
  }
  deriving
    ( Functor, Applicative, Monad, MonadState CodeGenState, L.MonadModuleBuilder
    , MonadIO, MonadFix
    )

instance MonadCodeGen CodeGenM where
  function name argsTys retTy body = do
    _ <- L.function
      (L.mkName name)
      (map (flip (,) L.NoParameterName) argsTys)
      retTy
      (const body)
    modify $ Env.insert $ Function name argsTys retTy

  lookup k = Env.lookup k <$> get

  typeDef name ty = do
    _ <- L.typedef (L.mkName name) (Just ty)
    modify $ Env.insert $ Type name ty

  emptyConstructor name retTy tag maxSize = do
    L.global
      (L.mkName name)
      retTy
      (L.Struct (Just (L.mkName name)) False  [L.Int 32 tag, L.Array (L.IntegerType 8) (replicate (fromIntegral maxSize) (L.Int 8 0))])
    modify $ Env.insert $ Constructor name retTy tag EmptyConstructor

  functionConstructor name argsTys ty retTy tag body = do
    _ <- L.function
      (L.mkName name)
      (map (flip (,) L.NoParameterName) argsTys)
      retTy
      (const body)
    modify $ Env.insert $ Constructor name retTy tag $ FunctionConstructor argsTys ty

runCodeGen :: CodeGenM a -> L.ModuleBuilderT IO a
runCodeGen = flip evalStateT Env.empty . unCodeGenM
