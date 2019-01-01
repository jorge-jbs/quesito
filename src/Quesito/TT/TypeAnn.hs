module Quesito.TT.TypeAnn where

import Quesito
import Quesito.TT
import Quesito.TT.Eval hiding (Env, TContext)
import qualified Quesito.Ann as Ann

import Data.List (find)
import Control.Monad (unless)

type TContext =
  [ ( Name  -- ^ var
    , Value  -- ^ type
    , Ann.Term Ann.Name  -- ^ annotated type
    )
  ]

type Env =
  [ ( Name
    , Def Value Value
    , Ann.Term Ann.Name
    )
  ]

discardThird :: [(a, b, c)] -> [(a, b)]
discardThird = map (\(x, y, _) -> (x, y))

typeInfAnn
  :: Env
  -> TContext
  -> Term Name
  -> Ques
       ( Value
       , Ann.Term Ann.Name  -- ^ Anntated input term
       )
typeInfAnn env ctx (Bound x) =
  case find (\(x', _, _) -> x == x') ctx of
    Just (_, ty, annTy) ->
      return (ty, Ann.Bound x annTy)
    Nothing -> do
      loc <- getLocation
      tell [show $ map (\(v, _, _) -> v) env]
      tell [show $ map (\(v, _, _) -> v) ctx]
      throwError ("Bound variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn env ctx (Free x) =
  case find (\(x', _, _) -> x == x') env of
    Just (_, DExpr _ ty, annTy) ->
      return (ty, Ann.Free x annTy)
    Just (_, DDataType ty, _) -> do
      qty <- quote ty
      (_, tyAnn) <- typeInfAnn env ctx qty
      return (ty, Ann.Free x tyAnn)
    Just (_, DDataCons ty, _) -> do
      qty <- quote ty
      (_, tyAnn) <- typeInfAnn env ctx qty
      return (ty, Ann.Free x tyAnn)
    Just (_, DMatchFunction _ ty, annTy) ->
      return (ty, Ann.Free x annTy)
    Nothing -> do
      loc <- getLocation
      tell [show $ map (\(v, _, _) -> v) env]
      tell [show $ map (\(v, _, _) -> v) ctx]
      throwError ("Free variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn _ _ (Type i) =
  return (VType (i + 1), Ann.Type i)
typeInfAnn _ _ (BytesType n) =
  return (VType 0, Ann.BytesType n)
typeInfAnn _ _ (Num n) = do
  loc <- getLocation
  throwError ("Cannot infer byte size of number " ++ show n ++ ": " ++ pprint loc)
typeInfAnn env ctx (Pi x e f) = do
  (ty, _) <- typeInfAnn env ctx e
  case ty of
    VType i -> do
      e' <- eval (discardThird env) [] e
      annE <- snd <$> typeInfAnn env ctx e
      (t', annF) <-
        typeInfAnn
          env
          ((x, e', annE) : ctx)
          (subst x (Free x) f)
      case t' of
        VType j ->
          return (VType (max i j), Ann.Pi x annE annF)
        _ -> do
          loc <- getLocation
          throwError ("1: " ++ pprint loc)
    _ -> do
      loc <- getLocation
      throwError ("2: " ++ pprint loc)
typeInfAnn env ctx (App e f) = do
  (s, annE) <- typeInfAnn env ctx e
  annS <- snd <$> (typeInfAnn env ctx =<< quote s)
  case s of
    VPi _ t t' -> do
      (annF, annT) <- typeCheckAnn env ctx f t
      f' <- eval (discardThird env) [] f
      x <- t' f'
      return (x, Ann.App (Ann.Ann annE annS) (Ann.Ann annF annT))
    _ -> do
      loc <- getLocation
      qs <- quote s
      throwError ("Applying to non-function at " ++ pprint loc ++ ": " ++ show qs)
typeInfAnn env ctx (Ann e ty) = do
  (tyTy, _) <- typeInfAnn env ctx ty
  case tyTy of
    VType _ -> do
      ty' <- eval (discardThird env) [] ty
      (annE, _) <- typeCheckAnn env ctx e ty'
      return (ty', annE)
    _ ->
      throwError ""
typeInfAnn _ _ e@(Lam _ _) =
  throwError ("Can't infer type of lambda expression " ++ show e)
typeInfAnn env ctx (Loc loc t) = do
  tell ["typeInfAnn Loc: " ++ show t]
  typeInfAnn env ctx t `locatedAt` loc

typeCheckAnn
  :: Env
  -> TContext
  -> Term Name  -- ^ expr
  -> Value  -- ^ type
  -> Ques
       ( Ann.Term Ann.Name  -- ^ annotated expr
       , Ann.Term Ann.Name  -- ^ annotated type
       )
typeCheckAnn env ctx (Lam x e) (VPi x' v w) = do
  tell ["typeInfAnn Lam: " ++ show e]
  w' <- w (VBound x)
  (_, annV) <- typeInfAnn env ctx =<< quote v
  (annE, annW') <- typeCheckAnn env ((x, v, annV) : ctx) (subst x (Bound x) e) w'
  return (Ann.Lam x annV (Ann.Ann annE annW'), Ann.Pi x' annV annW')
typeCheckAnn _ _ (Lam _ _) _ = do
  loc <- getLocation
  throwError ("6: " ++ pprint loc)
typeCheckAnn _ _ (Num x) (VBytesType n) =
  if x >= 0 && x < (2^(n*8)) then
    return (Ann.Num x n, Ann.BytesType n)
  else do
    loc <- getLocation
    if x < 0 then
      throwError ("Bytes cannot be negative numbers: " ++ pprint loc)
    else
      throwError ("Number " ++ show x ++ " is larger than byte size: " ++ pprint loc)
typeCheckAnn env ctx t (VType j) = do
  (t', annT) <- typeInfAnn env ctx t
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
typeCheckAnn env ctx (Loc loc t) ty = do
  tell ["typeInfAnn Loc: " ++ show t]
  typeCheckAnn env ctx t ty `locatedAt` loc
typeCheckAnn env ctx t ty = do
  (ty', annT) <- typeInfAnn env ctx t
  qty <- quote ty
  (_, annTy) <- typeInfAnn env ctx qty
  qty' <- quote ty'
  loc <- getLocation
  unless
    (deBruijnize qty == deBruijnize qty')
    (throwError ("Type mismatch at " ++ pprint loc ++ ". Expected " ++ show qty ++ " and got " ++ show qty'))
  return (annT, annTy)
