{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT
  ( -- * Types
    Name
  , Term(..)
  , mapInLoc
  , remLoc
  , deBruijnize
  , BinOp(..)
  , UnOp(..)
  )
  where

import Quesito

import Prelude hiding (print)

type Name = String

data Term v
  = Local v
  | Global Name
  | Type Int
  | BytesType Int
  | Num Int
  | BinOp BinOp
  | UnOp UnOp
  | Pi v (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam v (Term v)
  | Loc Location (Term v)
  deriving Show

data BinOp = Add | Sub | Mul | UDiv | SDiv | And | Or | Xor | Shr | Shl
  deriving Show

data UnOp = Not
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
  pprint (Local v) =
    pprint v
  pprint (Global v) =
    pprint v
  pprint (BytesType n) =
    "(" ++ "Bytes " ++ show n ++ ")"
  pprint (Num x) =
    show x
  pprint (BinOp Add) =
    "add"
  pprint (BinOp Sub) =
    "sub"
  pprint (BinOp _) =
    "hue"
  pprint (Type i) =
    "(" ++ "Type " ++ show i ++ ")"
  pprint (Pi n t t')
    | length (pprint n) == 0 =
      "(" ++ pprint t ++ " -> " ++ pprint t' ++ ")"
    | otherwise =
      "(" ++ "(" ++ pprint n ++ " : "++ pprint t ++ ") -> " ++ pprint t' ++ ")"
  pprint (App t t') =
    "(" ++ pprint t ++ " " ++ pprint t' ++ ")"
  pprint (Ann t t') =
    "(" ++ pprint t ++ " " ++ pprint t' ++ ")"
  pprint (Lam n t) =
    "(" ++ "\\" ++ pprint n ++ " -> " ++ pprint t ++ ")"
  pprint (Loc _ t) =
    pprint t

instance Eq v => Eq (Term v) where
  Loc _ t == t' =
    t == t'
  t == Loc _ t' =
    t == t'
  Local v == Local w =
    v == w
  Global v == Global w =
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
    deBruijnize' vars (Local v) =
      case takeWhile (\v' -> v /= v') vars of
        [] ->
          Local (DBFree v)
        xs ->
          Local (Index (length xs))
    deBruijnize' _ (Global v) =
      Global v
    deBruijnize' vars (Pi n t t') =
      Pi (Index 0) (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      Lam (Index 0) (deBruijnize' (n : vars) t)
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
