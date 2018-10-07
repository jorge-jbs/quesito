module Quesito.TT.TypeCheck where

import Quesito
import Quesito.TT
import Quesito.TT.Eval

import Data.List (find)
import Control.Monad (unless)

typeInf :: Env -> TContext -> Term Name -> Ques Value
typeInf env ctx (Bound x) =
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
          throwError ("Free variable at " ++ show loc ++ ": " ++ x)
typeInf env ctx (Free x) =
  typeInf env ctx (Bound x)
typeInf _ _ (Type i) =
  return (VType (i + 1))
typeInf env ctx (Pi x e f) = do
  t <- typeInf env ctx e
  case t of
    VType i -> do
      e' <- eval env [] e
      t' <-
        typeInf
          env
          ((x, e') : ctx)
          (subst x (Free x) f)
      case t' of
        VType j ->
          return (VType (max i j))
        _ -> do
          loc <- getLocation
          throwError ("1: " ++ show loc)
    _ -> do
      loc <- getLocation
      throwError ("2: " ++ show loc)
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
      throwError ("Applying to non-function at " ++ show loc ++ ": " ++ show qs)
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
  w' <- w (VFree x)
  typeCheck env ((x, v) : ctx) (subst x (Free x) e) w'
typeCheck _ _ (Lam _ _) _ = do
  loc <- getLocation
  throwError ("6: " ++ show loc)
typeCheck env ctx t (VType j) = do
  t' <- typeInf env ctx t
  case t' of
    VType i  ->
      if i <= j then
        return ()
      else do
        loc <- getLocation
        throwError ("Incorrect type universe at " ++ show loc ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v -> do
      loc <- getLocation
      qv <- quote v
      throwError ("Expected type at " ++ show loc ++ " and got: " ++ show qv)
typeCheck env ctx (Loc loc t) ty =
  typeCheck env ctx t ty `locatedAt` loc
typeCheck env ctx t ty = do
  ty' <- typeInf env ctx t
  qty <- quote ty
  qty' <- quote ty'
  loc <- getLocation
  unless
    (deBruijnize qty == deBruijnize qty')
    (throwError ("Type mismatch at " ++ show loc ++ ". Expected " ++ show qty ++ " and got " ++ show qty'))

