module Quesito.Ann where

import Quesito
import qualified Quesito.TT as TT

import Data.List (find)

type Name = TT.Name

data Term v
  = Var v (Term v)
  | Type Int
  | BytesType Int
  | Num Int
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam TT.Name (Term v)
  | Loc Location (Term v)
  deriving Show

type Context v =
  [(Name, Term Name)]

annotate :: Context Name -> TT.Term TT.Name -> Ques (Term Name)
annotate ctx (TT.Bound v) =
  case snd <$> find ((==) v . fst) ctx of
    Just ty ->
      return (Var v ty)
    Nothing -> do
      loc <- getLocation
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Could not find of variable " ++ v ++ " at " ++ show loc)
annotate ctx (TT.Free v) =
  annotate ctx (TT.Bound v)
annotate ctx (TT.Pi v p q) = do
  p' <- annotate ctx p
  q' <- annotate ((v, p') : ctx) q
  return (Pi v p' q')
annotate ctx (TT.App p q) =
  App <$> annotate ctx p <*> annotate ctx q
annotate ctx (TT.Ann t ty) =
  Ann <$> annotate ctx t <*> annotate ctx ty
annotate _ (TT.Lam v _) = do
  loc <- getLocation
  throwError ("Can't infer type of lambda variable " ++ v ++ " at " ++ show loc)
annotate ctx (TT.Loc loc t) =
  Loc loc <$> annotate ctx t `locatedAt` loc
annotate _ (TT.Type lvl) = return (Type lvl)
annotate _ (TT.BytesType n) = return (BytesType n)
annotate _ (TT.Num n) = return (Num n)
