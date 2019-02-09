module Quesito.Ann where

import Quesito
import Quesito.TT (BinOp(..), UnOp(..))
import qualified Quesito.TT as TT

data Term
  = Local String Term
  | Global String Term
  | Type Int
  | BytesType Int
  | BinOp BinOp
  | UnOp UnOp
  | Num { num :: Int, bytes :: Int }
  | Pi String Type Type
  | App Term Type Term Type
  | Lam String Term Term Type
  | Loc Location Term
  deriving Show

type Type = Term

downgrade :: Term -> TT.Term
downgrade (Local v _) =
  TT.Local v
downgrade (Global v _) =
  TT.Global v
downgrade (Type n) =
  TT.Type n
downgrade (BytesType n) =
  TT.BytesType n
downgrade (BinOp op) =
  TT.BinOp op
downgrade (UnOp op) =
  TT.UnOp op
downgrade (Num n _) =
  TT.Num n
downgrade (Pi v s t) =
  TT.Pi v (downgrade s) (downgrade t)
downgrade (App s _ t _) =
  TT.App (downgrade s) (downgrade t)
downgrade (Lam v _ t _) =
  TT.Lam v (downgrade t)
downgrade (Loc loc t) =
  TT.Loc loc (downgrade t)

substLocal :: String -> Term -> Term -> Term
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
substLocal name term (App t tTy t' tTy') =
  App (substLocal name term t) (substLocal name term tTy) (substLocal name term t') (substLocal name term tTy')
substLocal name term (Lam name' ty t tTy) =
  if name == name' then
    Lam name' ty t tTy
  else
    Lam name' (substLocal name term ty) (substLocal name term t) (substLocal name term tTy)
substLocal name term (Loc loc t) =
  Loc loc (substLocal name term t)

substGlobal :: String -> Term -> Term -> Term
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
substGlobal name term (App t tTy t' tTy') =
  App (substGlobal name term t) (substGlobal name term tTy) (substGlobal name term t') (substGlobal name term tTy')
substGlobal name term (Lam name' ty t tTy) =
  Lam name' (substGlobal name term ty) (substGlobal name term t) (substGlobal name term tTy)
substGlobal name term (Loc loc t) =
  Loc loc (substGlobal name term t)
