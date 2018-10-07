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

class Printable a where
  print :: a -> String

type Name = String

instance Printable Name where
  print n =
    n

data Term v
  = Bound v
  | Free v
  | Type Int
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam Name (Term v)
  | Loc Location (Term v)

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

instance Printable v => Show (Term v) where
  show (Bound v) =
    print v
  show (Free v) =
    print v
  show (Type i) =
    "(" ++ "Type " ++ show i ++ ")"
  show (Pi "" t t') =
    "(" ++ show t ++ " -> " ++ show t' ++ ")"
  show (Pi n t t') =
    "(" ++ "(" ++ n ++ " : "++ show t ++ ") -> " ++ show t' ++ ")"
  show (App t t') =
    "(" ++ show t ++ " " ++ show t' ++ ")"
  show (Ann t t') =
    "(" ++ show t ++ " " ++ show t' ++ ")"
  show (Lam n t) =
    "(" ++ "\\" ++ n ++ " -> " ++ show t ++ ")"
  show (Loc t _) =
    show t

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
