{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT
  ( -- * Types
    Name
  , Term(..)
  , mapInLoc
  , remLoc
  , deBruijnize
  , subst
  , freeVars
  )
  where

import Quesito

import Prelude hiding (print)
import Data.Foldable (foldl')

type Name = String

data Term v
  = Bound v
  | Free v
  | Type Int
  | BytesType Int
  | Num Int
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam Name (Term v)
  | Loc Location (Term v)
  deriving Show

mapInLoc :: Term v -> (Term v -> Term v) -> Term v
mapInLoc (Loc loc t) f =
  Loc loc (mapInLoc t f)
mapInLoc t f =
  f t

remLoc :: Term v -> Term v
remLoc (Loc _ t) =
  remLoc t
remLoc t =
  t

instance PPrint Name where
  pprint name =
    name

instance PPrint v => PPrint (Term v) where
  pprint (Bound v) =
    pprint v
  pprint (Free v) =
    pprint v
  pprint (BytesType n) =
    "(" ++ "Bytes " ++ show n ++ ")"
  pprint (Num x) =
    show x
  pprint (Type i) =
    "(" ++ "Type " ++ show i ++ ")"
  pprint (Pi "" t t') =
    "(" ++ pprint t ++ " -> " ++ pprint t' ++ ")"
  pprint (Pi n t t') =
    "(" ++ "(" ++ n ++ " : "++ pprint t ++ ") -> " ++ pprint t' ++ ")"
  pprint (App t t') =
    "(" ++ pprint t ++ " " ++ pprint t' ++ ")"
  pprint (Ann t t') =
    "(" ++ pprint t ++ " " ++ pprint t' ++ ")"
  pprint (Lam n t) =
    "(" ++ "\\" ++ n ++ " -> " ++ pprint t ++ ")"
  pprint (Loc _ t) =
    pprint t

instance Eq v => Eq (Term v) where
  Loc _ t == t' =
    t == t'
  t == Loc _ t' =
    t == t'
  Bound v == Bound w =
    v == w
  Free v == Free w =
    v == w
  Type i == Type j =
    i == j
  BytesType n == BytesType m =
    n == m
  Num x == Num y =
    x == y
  Pi v s s' == Pi w t t' =
    v == w && s == t && s' == t'
  App s s' == App t t' =
    s == t && s' == t'
  Ann s sty == Ann t tty =
    s == t && sty == tty
  _ == _ =
    False

data DeBruijnVar = Index Int | DBFree Name
  deriving Eq

deBruijnize :: Term Name -> Term DeBruijnVar
deBruijnize =
  deBruijnize' []
  where
    deBruijnize' :: [Name] -> Term Name -> Term DeBruijnVar
    deBruijnize' vars (Bound v) =
      case takeWhile (\v' -> v /= v') vars of
        [] ->
          Bound (DBFree v)
        xs ->
          Bound (Index (length xs))
    deBruijnize' _ (Free v) =
      Free (DBFree v)
    deBruijnize' vars (Pi n t t') =
      Pi "" (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      Lam "" (deBruijnize' (n : vars) t)
    deBruijnize' _ (Type i) =
      Type i
    deBruijnize' _ (BytesType n) =
      BytesType n
    deBruijnize' _ (Num n) =
      Num n
    deBruijnize' vars (App t t') =
      App (deBruijnize' vars t) (deBruijnize' vars t')
    deBruijnize' vars (Ann t t') =
      Ann (deBruijnize' vars t) (deBruijnize' vars t')
    deBruijnize' vars (Loc loc t) =
      Loc loc (deBruijnize' vars t)

subst :: Name -> Term Name -> Term Name -> Term Name
subst name term (Bound name') =
  if name == name' then
    term
  else
    Bound name'
subst _ _ (Free name') =
  Free name'
subst _ _ (Type level) =
  Type level
subst _ _ (BytesType n) =
  BytesType n
subst _ _ (Num n) =
  Num n
subst name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (subst name term t) (subst name term t')
subst name term (App t t') =
  App (subst name term t) (subst name term t')
subst name term (Ann t t') =
  Ann (subst name term t) (subst name term t')
subst name term (Lam name' t) =
  if name == name' then
    Lam name' t
  else
    Lam name' (subst name term t)
subst name term (Loc loc t) =
  Loc loc (subst name term t)

freeVars :: [Name] -> Term Name -> Term Name
freeVars vars term =
  foldl' (\term' v -> subst v (Free v) term') term vars
