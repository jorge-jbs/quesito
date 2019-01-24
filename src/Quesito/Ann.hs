module Quesito.Ann where

import Quesito
import qualified Quesito.TT as TT

type Name = TT.Name

data Term v
  = Local v (Term v)
  | Global Name (Term v)
  | Type Int
  | BytesType Int
  | Num { num :: Int, bytes :: Int }
  | Pi v (Term v) (Term v)
  | App (Ann Term v) (Ann Term v)
  | Lam v (Term v) (Ann Term v)
  | Loc Location (Term v)
  deriving Show

data Ann term v = Ann (term v) (term v)
  deriving Show

substLocal :: Eq v => v -> Term v -> Term v -> Term v
substLocal name term (Local name' ty) =
  if name == name' then
    term
  else
    Local name' ty
substLocal _ _ (Global name' ty) =
  Global name' ty
substLocal _ _ (Type level) =
  Type level
substLocal _ _ (BytesType n) =
  BytesType n
substLocal _ _ (Num n b) =
  Num n b
substLocal name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (substLocal name term t) (substLocal name term t')
substLocal name term (App (Ann t tTy) (Ann t' tTy')) =
  App (Ann (substLocal name term t) (substLocal name term tTy)) (Ann (substLocal name term t') (substLocal name term tTy'))
substLocal name term (Lam name' ty (Ann t tTy)) =
  if name == name' then
    Lam name' ty (Ann t tTy)
  else
    Lam name' (substLocal name term ty) (Ann (substLocal name term t) (substLocal name term tTy))
substLocal name term (Loc loc t) =
  Loc loc (substLocal name term t)

substGlobal :: Name -> Term v -> Term v -> Term v
substGlobal name term (Global name' ty) =
  if name == name' then
    term
  else
    Global name' ty
substGlobal _ _ (Local name' ty) =
  Local name' ty
substGlobal _ _ (Type level) =
  Type level
substGlobal _ _ (BytesType n) =
  BytesType n
substGlobal _ _ (Num n b) =
  Num n b
substGlobal name term (Pi name' t t') =
  Pi name' (substGlobal name term t) (substGlobal name term t')
substGlobal name term (App (Ann t tTy) (Ann t' tTy')) =
  App (Ann (substGlobal name term t) (substGlobal name term tTy)) (Ann (substGlobal name term t') (substGlobal name term tTy'))
substGlobal name term (Lam name' ty (Ann t tTy)) =
  Lam name' (substGlobal name term ty) (Ann (substGlobal name term t) (substGlobal name term tTy))
substGlobal name term (Loc loc t) =
  Loc loc (substGlobal name term t)
