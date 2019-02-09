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
import Quesito.TT.Eval hiding (Env, TContext)
import qualified Quesito.Ann as Ann

import Data.List (find)
import qualified Data.Map as Map
import Control.Monad (unless)
import Data.Default

type TContext =
  [ ( String -- ^ var
    , Value  -- ^ type
    , Ann.Term  -- ^ annotated type
    )
  ]

type Env =
  Map.Map String (Def Value Value, Ann.Term)

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
  :: Env
  -> TContext
  -> Term
  -> Ques
       ( Value
       , Ann.Term  -- ^ Anntated input term
       )
typeInfAnn = typeInfAnn' def


typeInfAnn'
  :: Options
  -> Env
  -> TContext
  -> Term
  -> Ques
       ( Value
       , Ann.Term  -- ^ Anntated input term
       )
typeInfAnn' opts env ctx (Local x) =
  case find (\(x', _, _) -> x == x') ctx of
    Just (_, ty, annTy) ->
      return (ty, Ann.Local x annTy)
    Nothing -> do
      loc <- getLocation
      tell [show $ Map.keys env]
      tell [show $ map (\(v, _, _) -> v) ctx]
      throwError ("Local variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn' opts env ctx (Global x) =
  case Map.lookup x env of
    Just (DDataType ty, _) -> do
      qty <- quote ty
      (_, tyAnn) <- typeInfAnn' opts env ctx qty
      return (ty, Ann.Global x tyAnn)
    Just (DDataCons ty, _) -> do
      qty <- quote ty
      (_, tyAnn) <- typeInfAnn' opts env ctx qty
      return (ty, Ann.Global x tyAnn)
    Just (DMatchFunction _ ty _, annTy) ->
      return (ty, Ann.Global x annTy)
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (Map.keys env)]
      tell ["ctx: " ++ show (map (\(v, _, _) -> v) ctx)]
      throwError ("Global variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn' opts _ _ (Type i) =
  return (VType (i + 1), Ann.Type i)
typeInfAnn' opts _ _ (BytesType n) =
  return (VType 0, Ann.BytesType n)
typeInfAnn' opts _ _ (Num n) = do
  loc <- getLocation
  throwError ("Cannot infer byte size of number " ++ show n ++ ": " ++ pprint loc)
typeInfAnn' opts _ _ (BinOp op) =
  return (VPi "" (VBytesType 4) (\_ -> return (VPi "" (VBytesType 4) (const (return (VBytesType 4))))), Ann.BinOp op)
typeInfAnn' opts _ _ (UnOp op) =
  return (VPi "" (VBytesType 4) (const (return (VBytesType 4))), Ann.UnOp op)
typeInfAnn' opts env ctx (Pi x e f) = do
  (ty, _) <- typeInfAnn' opts env ctx e
  case ty of
    VType i -> do
      e' <- eval (Map.map fst env) [] e
      annE <- snd <$> typeInfAnn' opts env ctx e
      (t', annF) <-
        typeInfAnn' opts
          env
          ((x, e', annE) : ctx)
          f
      case t' of
        VType j ->
          return (VType (max i j), Ann.Pi x annE annF)
        _ -> do
          loc <- getLocation
          throwError ("1: " ++ pprint loc)
    _ -> do
      loc <- getLocation
      throwError ("2: " ++ pprint loc)
typeInfAnn' opts env ctx (App e f) = do
  (s, annE) <- typeInfAnn' opts env ctx e
  annS <- snd <$> (typeInfAnn' opts env ctx =<< quote s)
  case s of
    VPi _ t t' -> do
      (annF, annT) <- typeCheckAnn' opts env ctx f t
      f' <- eval (Map.map fst env) [] f
      x <- t' f'
      return (x, Ann.App annE annS annF annT)
    _ -> do
      loc <- getLocation
      qs <- quote s
      throwError ("Applying to non-function at " ++ pprint loc ++ ": " ++ show qs)
typeInfAnn' opts env ctx (Ann e ty) = do
  (tyTy, _) <- typeInfAnn' opts env ctx ty
  case tyTy of
    VType _ -> do
      ty' <- eval (Map.map fst env) [] ty
      (annE, _) <- typeCheckAnn' opts env ctx e ty'
      return (ty', annE)
    _ ->
      throwError ""
typeInfAnn' opts _ _ e@(Lam _ _) =
  throwError ("Can't infer type of lambda expression " ++ show e)
typeInfAnn' opts env ctx (Loc loc t) = do
  tell ["typeInfAnn' opts Loc: " ++ show t]
  typeInfAnn' opts env ctx t `locatedAt` loc

typeCheckAnn
  :: Env
  -> TContext
  -> Term  -- ^ expr
  -> Value  -- ^ type
  -> Ques
       ( Ann.Term  -- ^ annotated expr
       , Ann.Term  -- ^ annotated type
       )
typeCheckAnn = typeCheckAnn' def

typeCheckAnn'
  :: Options
  -> Env
  -> TContext
  -> Term  -- ^ expr
  -> Value  -- ^ type
  -> Ques
       ( Ann.Term  -- ^ annotated expr
       , Ann.Term  -- ^ annotated type
       )
typeCheckAnn' opts env ctx t@(Local v) ty | inferVars opts = do
  (_, annTy) <- typeInfAnn' opts env ctx =<< quote ty
  return (Ann.Local v annTy, annTy)
typeCheckAnn' opts env ctx (Lam x e) (VPi x' v w) = do
  tell ["typeInfAnn' opts Lam: " ++ show e]
  w' <- w (VNormal (NFree x))
  (_, annV) <- typeInfAnn' opts env ctx =<< quote v
  (annE, annW') <- typeCheckAnn' opts env ((x, v, annV) : ctx) e w'
  return (Ann.Lam x annV annE annW', Ann.Pi x' annV annW')
typeCheckAnn' opts _ _ (Lam _ _) _ = do
  loc <- getLocation
  throwError ("6: " ++ pprint loc)
typeCheckAnn' opts _ _ (Num x) (VBytesType n) =
  if x >= 0 && fromIntegral x < (2^(n*8)) then
    return (Ann.Num x n, Ann.BytesType n)
  else do
    loc <- getLocation
    if x < 0 then
      throwError ("Bytes cannot be negative numbers: " ++ pprint loc)
    else
      throwError ("Number " ++ show x ++ " is larger than byte size (" ++ show n ++ "): " ++ pprint loc)
typeCheckAnn' opts env ctx t (VType j) = do
  (t', annT) <- typeInfAnn' opts env ctx t
  case t' of
    VType i  ->
      if i <= j then
        return (annT, Ann.Type j)
      else do
        loc <- getLocation
        throwError ("Incorrect type universe at " ++ pprint loc ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v -> do
      loc <- getLocation
      qv <- quote v
      throwError ("Expected type at " ++ pprint loc ++ " and got: " ++ show qv)
typeCheckAnn' opts env ctx (Loc loc t) ty = do
  tell ["typeInfAnn' opts Loc: " ++ show t]
  typeCheckAnn' opts env ctx t ty `locatedAt` loc
typeCheckAnn' opts env ctx t ty = do
  (ty', annT) <- typeInfAnn' opts env ctx t
  qty <- quote ty
  (_, annTy) <- typeInfAnn' opts env ctx qty
  qty' <- quote ty'
  loc <- getLocation
  unless
    (deBruijnize qty == deBruijnize qty')
    (throwError ("Type mismatch at " ++ pprint loc ++ ". Expected " ++ show qty ++ " and got " ++ show qty'))
  return (annT, annTy)
