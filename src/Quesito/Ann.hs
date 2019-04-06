module Quesito.Ann where

import Quesito (PPrint(..))
import Quesito.TT (BinOp(..), UnOp(..), Flags)
import Quesito.Env (Definition(..))
import qualified Quesito.TT as TT

data Term
  = Local String Type
  | Global String Type
  | Type Int
  | BytesType Int
  | BinOp BinOp
  | UnOp UnOp
  | Num
      Int -- ^ literal
      Int -- ^ bytes
  | Pi String Type Type
  | App Term Term
  | Lam String Type Term
  deriving Show

type Type = Term

instance PPrint Term where
  pprint = pprint . downgrade

data Def
  = PatternMatchingDef
      String  -- ^ name
      [([(String, Type)], [Pattern], Term)]  -- ^ equations
      Type  -- ^ type
      Flags
  | TypeDef
      String  -- ^ name
      Type  -- ^ type
      [(String, Term)]  -- ^ constructors
  deriving Show

instance Definition Def where
  getNames (PatternMatchingDef n _ _ _) =
    [n]
  getNames (TypeDef n _ conss) =
    n : map fst conss

data PatternG t
  = Binding String t
  | Inaccessible t
  | NumPat Int Int
  | NumSucc (PatternG t)
  | Constructor String
  | PatApp (PatternG t) (PatternG t)
  deriving Show

type Pattern = PatternG Term

flattenPatApp :: PatternG a -> [PatternG a]
flattenPatApp (PatApp r s) =
  flattenPatApp r ++ [s]
flattenPatApp t =
  [t]

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
downgrade (App s t) =
  TT.App (downgrade s) (downgrade t)
downgrade (Lam v _ t) =
  TT.Lam v (downgrade t)

typeInf :: Term -> Type
typeInf (Local _ ty) =
  ty
typeInf (Global _ ty) =
  ty
typeInf (Type i) =
  Type (i+1)
typeInf (BytesType _) =
  Type 0
typeInf (BinOp _) =
  Pi "" (BytesType 4) $ Pi "" (BytesType 4) (BytesType 4)
typeInf (UnOp _) =
  Pi "" (BytesType 4) (BytesType 4)
typeInf (Num _ b) =
  BytesType b
typeInf (Pi _ ty1 ty2) =
  case (typeInf ty1, typeInf ty2) of
    (Type i, Type j) ->
      Type $ max i j
    _ ->
      error ""
typeInf (App r s) =
  case typeInf r of
    Pi v _ ty2 ->
      substLocal v s ty2
    _ ->
      error ""
typeInf (Lam v ty t) =
  Pi v ty $ typeInf t

substLocal :: String -> Term -> Term -> Term
substLocal name term (Local name' ty) =
  if name == name' then
    term
  else
    Local name' ty
substLocal _ _ (Global name' ty) =
  Global name' ty
substLocal name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (substLocal name term t) (substLocal name term t')
substLocal name term (App t t') =
  App (substLocal name term t) (substLocal name term t')
substLocal name term (Lam name' ty t) =
  if name == name' then
    Lam name' ty t
  else
    Lam name' (substLocal name term ty) (substLocal name term t)
substLocal _ _ t =
  t

substGlobal :: String -> Term -> Term -> Term
substGlobal name term (Global name' ty) =
  if name == name' then
    term
  else
    Global name' ty
substGlobal _ _ (Local name' ty) =
  Local name' ty
substGlobal name term (Pi name' t t') =
  Pi name' (substGlobal name term t) (substGlobal name term t')
substGlobal name term (App t t') =
  App (substGlobal name term t) (substGlobal name term t')
substGlobal name term (Lam name' ty t) =
  Lam name' (substGlobal name term ty) (substGlobal name term t)
substGlobal _ _ t =
  t

flattenApp :: Term -> [Term]
flattenApp =
  flattenApp' []
  where
    flattenApp' :: [Term] -> Term -> [Term]
    flattenApp' as (App f a) =
      flattenApp' (a:as) f
    flattenApp' as f =
      f:as

flattenPi :: Type -> ([Type], Type)
flattenPi (Pi _ ty1 ty2) =
  let (args, ret) = flattenPi ty2
  in (ty1 : args, ret)
flattenPi t =
  ([], t)
