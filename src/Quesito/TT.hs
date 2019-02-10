{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT
  ( -- * Types
    Term(..)
  , Type
  , mapInLoc
  , remLoc
  , deBruijnize
  , flattenApp
  , BinOp(..)
  , UnOp(..)
  )
  where

import Quesito

import Prelude hiding (print)

data Term
  = Local String
  | Global String
  | Type Int
  | BytesType Int
  | Num Int
  | BinOp BinOp
  | UnOp UnOp
  | Pi String Term Term
  | App Term Term
  | Ann Term Term
  | Lam String Term
  | Loc Location Term
  deriving Show

type Type = Term

data BinOp = Add | Sub | Mul | UDiv | SDiv | And | Or | Xor | Shr | Shl
  deriving Show

data UnOp = Not
  deriving Show

mapInLoc :: Term -> (Term -> Term) -> Term
mapInLoc (Loc loc t) f =
  Loc loc (mapInLoc t f)
mapInLoc t f =
  f t

remLoc :: Term -> Term
remLoc (Loc _ t) =
  remLoc t
remLoc t =
  t

instance PPrint Term where
  pprint (Local v) =
    v
  pprint (Global v) =
    v
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
  pprint (UnOp Not) =
    "not"
  pprint (Type i) =
    "(" ++ "Type " ++ show i ++ ")"
  pprint (Pi v t t')
    | length v == 0 =
      "(" ++ pprint t ++ " -> " ++ pprint t' ++ ")"
    | otherwise =
      "(" ++ "(" ++ v ++ " : "++ pprint t ++ ") -> " ++ pprint t' ++ ")"
  pprint (App t t') =
    "(" ++ pprint t ++ " " ++ pprint t' ++ ")"
  pprint (Ann t t') =
    "(" ++ pprint t ++ " " ++ pprint t' ++ ")"
  pprint (Lam v t) =
    "(" ++ "\\" ++ v ++ " -> " ++ pprint t ++ ")"
  pprint (Loc _ t) =
    pprint t

instance Eq DeBrujnizedTerm where
  DBLoc _ t == t' =
    t == t'
  t == DBLoc _ t' =
    t == t'
  DBBound v == DBBound w =
    v == w
  DBFree v == DBFree w =
    v == w
  DBGlobal v == DBGlobal w =
    v == w
  DBType i == DBType j =
    i == j
  DBBytesType n == DBBytesType m =
    n == m
  DBNum x == DBNum y =
    x == y
  DBPi s s' == DBPi t t' =
    s == t && s' == t'
  DBApp s s' == DBApp t t' =
    s == t && s' == t'
  DBAnn s sty == DBAnn t tty =
    s == t && sty == tty
  _ == _ =
    False

data DeBrujnizedTerm
  = DBBound Int
  | DBFree String
  | DBGlobal String
  | DBType Int
  | DBBytesType Int
  | DBNum Int
  | DBBinOp BinOp
  | DBUnOp UnOp
  | DBPi DeBrujnizedTerm DeBrujnizedTerm
  | DBApp DeBrujnizedTerm DeBrujnizedTerm
  | DBAnn DeBrujnizedTerm DeBrujnizedTerm
  | DBLam DeBrujnizedTerm
  | DBLoc Location DeBrujnizedTerm
  deriving Show

deBruijnize :: Term -> DeBrujnizedTerm
deBruijnize =
  deBruijnize' []
  where
    deBruijnize' :: [String] -> Term -> DeBrujnizedTerm
    deBruijnize' vars (Local v) =
      case takeWhile (\v' -> v /= v') vars of
        [] ->
          DBFree v
        xs ->
          DBBound (length xs)
    deBruijnize' _ (Global v) =
      DBGlobal v
    deBruijnize' vars (Pi n t t') =
      DBPi (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      DBLam (deBruijnize' (n : vars) t)
    deBruijnize' _ (Type i) =
      DBType i
    deBruijnize' _ (BytesType n) =
      DBBytesType n
    deBruijnize' _ (Num n) =
      DBNum n
    deBruijnize' _ (BinOp op) =
      DBBinOp op
    deBruijnize' _ (UnOp op) =
      DBUnOp op
    deBruijnize' vars (App t t') =
      DBApp (deBruijnize' vars t) (deBruijnize' vars t')
    deBruijnize' vars (Ann t t') =
      DBAnn (deBruijnize' vars t) (deBruijnize' vars t')
    deBruijnize' vars (Loc loc t) =
      DBLoc loc (deBruijnize' vars t)

flattenApp :: Term -> [Term]
flattenApp =
  flattenApp' []
  where
    flattenApp' :: [Term] -> Term -> [Term]
    flattenApp' as (App f a) =
      flattenApp' (a:as) f
    flattenApp' as (Loc _ a) =
      flattenApp' as a
    flattenApp' as f =
      f:as
