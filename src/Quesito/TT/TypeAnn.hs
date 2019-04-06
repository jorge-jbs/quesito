{-# LANGUAGE FlexibleContexts #-}

module Quesito.TT.TypeAnn
  ( TContext
  , Env
  , Options(..)
  , typeInfAnn
  , typeCheckAnn
  , typeInfAnn'
  , typeCheckAnn'
  )
  where

import Quesito
import Quesito.TT
import Quesito.Ann.Eval hiding (TContext, Env)
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env

import Data.List (find)
import Control.Monad (unless)
import Data.Default

type TContext =
  [ ( String -- ^ var
    , Value  -- ^ type
    , Ann.Term  -- ^ annotated type
    )
  ]

type Env = Env.Env Ann.Def

data Options
  = Options
      { inferVars :: Bool
      }

instance Default Options where
  def =
    Options
      { inferVars = False
      }

typeInfAnn
  :: (MonadLog m, MonadExcept m, MonadEnv Ann.Def m, MonadLocatable m)
  => TContext
  -> Term
  -> m
       ( Value
       , Ann.Term  -- ^ annotated input term
       )
typeInfAnn = typeInfAnn' def

typeInfAnn'
  :: (MonadEnv Ann.Def m, MonadLog m, MonadExcept m, MonadLocatable m)
  => Options
  -> TContext
  -> Term
  -> m
       ( Value
       , Ann.Term  -- ^ annotated input term
       )
typeInfAnn' _ ctx (Local x) =
  case find (\(x', _, _) -> x == x') ctx of
    Just (_, ty, annTy) ->
      return (ty, Ann.Local x annTy)
    Nothing -> do
      loc <- getLocation
      env <- ask
      tell (show $ Env.keys env)
      tell (show $ map (\(v, _, _) -> v) ctx)
      throwError ("Local variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn' _ ctx (Global x) = do
  env <- ask
  case Env.lookup x env of
    Just (Ann.TypeDef n annTy _) | x == n -> do
      ty' <- eval [] annTy
      return (ty', Ann.Global x annTy)
    Just (Ann.TypeDef _ _ conss) ->
      case lookup x conss of
        Just annTy -> do
          ty' <- eval [] annTy
          return (ty', Ann.Global x annTy)
        Nothing -> do
          env <- ask
          tell ("env: " ++ show (Env.keys env))
          tell ("ctx: " ++ show (map (\(v, _, _) -> v) ctx))
          throwError "Internal error"
    Just (Ann.PatternMatchingDef _ _ annTy _) -> do
      ty' <- eval [] annTy
      return (ty', Ann.Global x annTy)
    Nothing -> do
      loc <- getLocation
      env <- ask
      tell ("env: " ++ show (Env.keys env))
      tell ("ctx: " ++ show (map (\(v, _, _) -> v) ctx))
      throwError ("Global variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn' _ _ (Type i) =
  return (VType (i + 1), Ann.Type i)
typeInfAnn' _ _ (BytesType n) =
  return (VType 0, Ann.BytesType n)
typeInfAnn' _ _ (Num n) = do
  loc <- getLocation
  throwError ("Cannot infer byte size of number " ++ show n ++ ": " ++ pprint loc)
typeInfAnn' _ _ (BinOp op) = do
  ty <- eval [] (Ann.Pi "" (Ann.BytesType 4) (Ann.Pi "" (Ann.BytesType 4) (Ann.BytesType 4)))
  return (ty, Ann.BinOp op)
typeInfAnn' _ _ (UnOp op) = do
  ty <- eval [] (Ann.Pi "" (Ann.BytesType 4) (Ann.BytesType 4))
  return (ty, Ann.UnOp op)
typeInfAnn' opts ctx (Pi x e f) = do
  (ty, annE) <- typeInfAnn' opts ctx e
  case ty of
    VType i -> do
      e' <- eval [] annE
      (t', annF) <- typeInfAnn' opts ((x, e', annE) : ctx) f
      case t' of
        VType j ->
          return (VType (max i j), Ann.Pi x annE annF)
        _ -> do
          loc <- getLocation
          throwError ("1: " ++ pprint loc)
    _ -> do
      loc <- getLocation
      throwError ("2: " ++ pprint loc)
typeInfAnn' opts ctx (App e f) = do
  (s, annE) <- typeInfAnn' opts ctx e
  case s of
    VPi v t t' (Closure ctx') -> do
      (annF, _) <- typeCheckAnn' opts ctx f t
      f' <- eval [] annF
      x <- eval ((v, f') : ctx') t'
      return (x, Ann.App annE annF)
    _ -> do
      loc <- getLocation
      let qs = quote s
      throwError ("Applying to non-function at " ++ pprint loc ++ ": " ++ show qs)
typeInfAnn' opts ctx (Ann e ty) = do
  (tyTy, annTy) <- typeInfAnn' opts ctx ty
  case tyTy of
    VType _ -> do
      ty' <- eval [] annTy
      (annE, _) <- typeCheckAnn' opts ctx e ty'
      return (ty', annE)
    _ ->
      throwError ""
typeInfAnn' _ _ e@(Lam _ _) =
  throwError ("Can't infer type of lambda expression " ++ show e)
typeInfAnn' opts ctx (Loc loc t) = do
  tell ("typeInfAnn' opts Loc: " ++ show t)
  typeInfAnn' opts ctx t `locatedAt` loc

typeCheckAnn
  :: (MonadLog m, MonadExcept m, MonadEnv Ann.Def m, MonadLocatable m)
  => TContext
  -> Term  -- ^ expr
  -> Value  -- ^ type
  -> m
       ( Ann.Term  -- ^ annotated expr
       , Ann.Term  -- ^ annotated type
       )
typeCheckAnn = typeCheckAnn' def

typeCheckAnn'
  :: (MonadLog m, MonadExcept m, MonadEnv Ann.Def m, MonadLocatable m)
  => Options
  -> TContext
  -> Term  -- ^ expr
  -> Value  -- ^ type
  -> m
       ( Ann.Term  -- ^ annotated expr
       , Ann.Term  -- ^ annotated type
       )
typeCheckAnn' opts _ (Local v) ty | inferVars opts = do
  let annTy = quote ty
  return (Ann.Local v annTy, annTy)
typeCheckAnn' opts ctx (Lam x e) (VPi x' v w (Closure ctx')) = do
  tell ("typeInfAnn' opts Lam: " ++ show e)
  w' <- eval ctx' w
  let annV = quote v
  (annE, annW') <- typeCheckAnn' opts ((x, v, annV) : ctx) e w'
  return (Ann.Lam x annV annE, Ann.Pi x' annV annW')
typeCheckAnn' _ _ (Lam _ _) _ = do
  loc <- getLocation
  throwError ("6: " ++ pprint loc)
typeCheckAnn' _ _ (Num x) (VBytesType n) =
  if x >= 0 && fromIntegral x < (2^(n*8) :: Integer) then
    return (Ann.Num x n, Ann.BytesType n)
  else do
    loc <- getLocation
    if x < 0 then
      throwError ("Bytes cannot be negative numbers: " ++ pprint loc)
    else
      throwError ("Number " ++ show x ++ " is larger than byte size (" ++ show n ++ "): " ++ pprint loc)
typeCheckAnn' opts ctx t (VType j) = do
  (t', annT) <- typeInfAnn' opts ctx t
  case t' of
    VType i  ->
      if i <= j then
        return (annT, Ann.Type j)
      else do
        loc <- getLocation
        throwError ("Incorrect type universe at " ++ pprint loc ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v -> do
      loc <- getLocation
      let qv = quote v
      throwError ("Expected type at " ++ pprint loc ++ " and got: " ++ show qv)
typeCheckAnn' opts ctx (Loc loc t) ty = do
  tell ("typeInfAnn' opts Loc: " ++ show t)
  typeCheckAnn' opts ctx t ty `locatedAt` loc
typeCheckAnn' opts ctx t ty = do
  (ty', annT) <- typeInfAnn' opts ctx t
  let qty = quote ty
      qty' = quote ty'
  loc <- getLocation
  unless
    (deBruijnize (Ann.downgrade qty) == deBruijnize (Ann.downgrade qty'))
    (throwError ("Type mismatch at " ++ pprint loc ++ ". Expected " ++ pprint qty ++ " and got " ++ pprint qty'))
  return (annT, qty)
