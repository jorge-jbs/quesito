module Quesito.TT.TypeCheck where

import Quesito
import Quesito.TT
import Quesito.TT.Eval

import Data.List (find)
import Control.Monad (unless)

typeInf :: Env -> TContext -> Term Name -> Ques Value
typeInf env ctx (Local x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      return v
    Nothing ->
      case snd <$> find ((==) x . fst) env of
        Just (DExpr _ ty) ->
          return ty
        Just (DDataType ty) ->
          return ty
        Just (DDataCons ty) ->
          return ty
        Just (DMatchFunction _ ty) ->
          return ty
        Nothing -> do
          loc <- getLocation
          throwError ("Global variable at " ++ pprint loc ++ ": " ++ x)
typeInf env ctx (Global x) =
  typeInf env ctx (Local x)
typeInf _ _ (Type i) =
  return (VType (i + 1))
typeInf _ _ (BytesType _) =
  return (VType 0)
typeInf _ _ (Num n) = do
  loc <- getLocation
  throwError ("Cannot infer byte size of number " ++ show n ++ ": " ++ pprint loc)
typeInf env ctx (Pi x e f) = do
  t <- typeInf env ctx e
  case t of
    VType i -> do
      e' <- eval env [] e
      t' <-
        typeInf
          env
          ((x, e') : ctx)
          f
      case t' of
        VType j ->
          return (VType (max i j))
        _ -> do
          loc <- getLocation
          throwError ("1: " ++ pprint loc)
    _ -> do
      loc <- getLocation
      throwError ("2: " ++ pprint loc)
typeInf env ctx (App e f) = do
  s <- typeInf env ctx e
  case s of
    VPi _ t t' -> do
      typeCheck env ctx f t
      f' <- eval env [] f
      t' f'
    _ -> do
      loc <- getLocation
      qs <- quote s
      throwError ("Applying to non-function at " ++ pprint loc ++ ": " ++ show qs)
typeInf env ctx (Ann e ty) = do
  tyTy <- typeInf env ctx ty
  case tyTy of
    VType _ -> do
      ty' <- eval env [] ty
      typeCheck env ctx e ty'
      return ty'
    _ ->
      throwError ""
typeInf _ _ e@(Lam _ _) =
  throwError ("Can't infer type of lambda expression " ++ show e)
typeInf env ctx (Loc loc t) =
  typeInf env ctx t `locatedAt` loc

typeCheck :: Env -> TContext -> Term Name -> Value -> Ques ()
typeCheck env ctx (Lam x e) (VPi _ v w) = do
  w' <- w (VGlobal x)
  typeCheck env ((x, v) : ctx) e w'
typeCheck _ _ (Lam _ _) _ = do
  loc <- getLocation
  throwError ("6: " ++ pprint loc)
typeCheck _ _ (Num x) (VBytesType n) =
  if x >= 0 && x < (2^(n*8)) then
    return ()
  else do
    loc <- getLocation
    if x < 0 then
      throwError ("Bytes cannot be negative numbers: " ++ pprint loc)
    else
      throwError ("Number " ++ show x ++ " is larger than byte size: " ++ pprint loc)
typeCheck env ctx t (VType j) = do
  t' <- typeInf env ctx t
  case t' of
    VType i  ->
      if i <= j then
        return ()
      else do
        loc <- getLocation
        throwError ("Incorrect type universe at " ++ pprint loc ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v -> do
      loc <- getLocation
      qv <- quote v
      throwError ("Expected type at " ++ pprint loc ++ " and got: " ++ show qv)
typeCheck env ctx (Loc loc t) ty =
  typeCheck env ctx t ty `locatedAt` loc
typeCheck env ctx t ty = do
  ty' <- typeInf env ctx t
  qty <- quote ty
  qty' <- quote ty'
  loc <- getLocation
  unless
    (deBruijnize qty == deBruijnize qty')
    (throwError ("Type mismatch at " ++ pprint loc ++ ". Expected " ++ show qty ++ " and got " ++ show qty'))
