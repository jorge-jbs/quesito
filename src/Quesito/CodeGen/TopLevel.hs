{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Quesito.CodeGen.TopLevel where

import Prelude hiding (lookup)
import Control.Monad.State (StateT, MonadState, evalStateT, get, modify)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Fix (MonadFix)

import qualified LLVM.AST as L hiding (function)
import qualified LLVM.IRBuilder.Module as L
import qualified LLVM.IRBuilder.Monad as L

import qualified Quesito.Env as Env

data Constructor
  = EmptyConstructor String Integer
  | FunctionConstructor
      String
      [L.Type]  -- ^ arguments types
      L.Type  -- ^ struct
      Integer  -- ^ tag
  deriving Show

getTag :: Constructor -> Integer
getTag (EmptyConstructor _ tag) = tag
getTag (FunctionConstructor _ _ _ tag) = tag

data Def
  = Function
      String  -- ^ name
      [L.Type]  -- ^ arguments types
      L.Type  -- ^ return type
  | Constructor Constructor
  | Type
      String  -- ^ name
      L.Type
  deriving Show

instance Env.Definition Def where
  getNames (Function n _ _) =
    [n]
  getNames (Constructor (EmptyConstructor n _)) =
    [n]
  getNames (Constructor (FunctionConstructor n _ _ _)) =
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
  emptyConstructor :: String -> Integer -> m ()

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

  typeDef name ty =
    modify $ Env.insert $ Type name ty

  emptyConstructor name tag =
    modify $ Env.insert $ Constructor $ EmptyConstructor name tag

  functionConstructor name argsTys ty retTy tag body = do
    _ <- L.function
      (L.mkName name)
      (map (flip (,) L.NoParameterName) argsTys)
      retTy
      (const body)
    modify $ Env.insert $ Constructor $ FunctionConstructor name argsTys ty tag

runCodeGen :: CodeGenM a -> L.ModuleBuilderT IO a
runCodeGen = flip evalStateT Env.empty . unCodeGenM
