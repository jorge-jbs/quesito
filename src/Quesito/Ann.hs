module Quesito.Ann where

import Quesito
import qualified Quesito.TT as TT

import Data.List (find)

type Name = TT.Name

data Term v
  = Bound v (Term v)
  | Free v (Term v)
  | Type Int
  | BytesType Int
  | Num { num :: Int, bytes :: Int }
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam TT.Name (Term v) (Term v) (Term v)
  | Loc Location (Term v)
  deriving Show

type Context v =
  [(Name, Term Name)]

annotate' :: Context Name -> Context Name -> TT.Term TT.Name -> TT.Term TT.Name -> Ques (Term Name)
annotate' env ctx t (TT.Loc _ ty) =
  annotate' env ctx t ty
annotate' env ctx (TT.Bound v) _ =
  case snd <$> find ((==) v . fst) ctx of
    Just ty ->
      return (Bound v ty)
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (map fst env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Could not find bound variable " ++ v ++ " at " ++ pprint loc)
annotate' env ctx (TT.Free v) _ =
  case snd <$> find ((==) v . fst) env of
    Just ty ->
      return (Free v ty)
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (map fst env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Could not find free variable " ++ v ++ " at " ++ pprint loc)
annotate' env ctx (TT.Pi v p q) _ = do
  p' <- annotate env ctx p
  q' <- annotate env ((v, p') : ctx) q
  return (Pi v p' q')
annotate' env ctx (TT.App p q) _ =
  App <$> annotate env ctx p <*> annotate env ctx q
annotate' env ctx (TT.Ann t ty) _ =
  Ann <$> annotate' env ctx t ty <*> annotate env ctx ty
annotate' env ctx (TT.Lam v body) (TT.Pi _ ty1 ty2) = do
  ty1' <- annotate env ctx ty1
  ty2' <- annotate env ctx ty2
  flip (Lam v ty1') ty2' <$> annotate' env ((v, ty1') : ctx) body ty2
annotate' _ _ t@(TT.Lam _ _) ty = do
  loc <- getLocation
  tell [show t, show ty]
  throwError ("Can't infer type of lambda expression " ++ pprint t ++ " at " ++ pprint loc)
annotate' env ctx (TT.Loc loc t) ty =
  Loc loc <$> annotate' env ctx t ty `locatedAt` loc
annotate' _ _ (TT.Type lvl) _ =
  return (Type lvl)
annotate' _ _ (TT.BytesType n) _ =
  return (BytesType n)
annotate' _ _ (TT.Num n) (TT.BytesType bytes') =
  return (Num n bytes')
annotate' _ _ (TT.Num n) _ = do
  loc <- getLocation
  throwError ("Could not infer type of number literal " ++ show n ++ " at " ++ pprint loc)

annotate :: Context Name -> Context Name -> TT.Term TT.Name -> Ques (Term Name)
annotate env ctx (TT.Bound v) =
  case snd <$> find ((==) v . fst) ctx of
    Just ty ->
      return (Bound v ty)
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (map fst env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Could not find bound variable " ++ v ++ " at " ++ pprint loc)
annotate env ctx (TT.Free v) =
  case snd <$> find ((==) v . fst) env of
    Just ty ->
      return (Free v ty)
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (map fst env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Could not find free variable " ++ v ++ " at " ++ pprint loc)
annotate env ctx (TT.Pi v p q) = do
  p' <- annotate env ctx p
  q' <- annotate env ((v, p') : ctx) q
  return (Pi v p' q')
annotate env ctx (TT.App p q) =
  App <$> annotate env ctx p <*> annotate env ctx q
annotate env ctx (TT.Ann t ty) = do
  ty' <- annotate env ctx ty
  flip Ann ty' <$> annotate' env ctx t ty
annotate _ _ (TT.Lam v _) = do
  loc <- getLocation
  throwError ("Can't infer type of lambda variable " ++ v ++ " at " ++ pprint loc)
annotate env ctx (TT.Loc loc t) =
  Loc loc <$> annotate env ctx t `locatedAt` loc
annotate _ _ (TT.Type lvl) =
  return (Type lvl)
annotate _ _ (TT.BytesType n) =
  return (BytesType n)
annotate _ _ (TT.Num n) = do
  loc <- getLocation
  throwError ("Could not infer type of number literal " ++ show n ++ " at " ++ pprint loc)
