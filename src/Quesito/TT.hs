{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT
  ( -- * Types
    Term(..)
  , Type
  , mapInLoc
  , remLoc
  , flattenApp
  , AttrLit(..)
  , BinOp(..)
  , UnOp(..)
  , Def(..)
  , Flags(..)
  , Pattern(..)
  , deBruijnize
  )
  where

import Prelude hiding (print)

import Quesito
import Quesito.Env (Definition(..))

data Term
  = Local String
  | Meta String
  | Global String
  | BaseType Int
  | UniquenessAttr
  | AttrLit AttrLit
  | Type
      Int  -- ^ universe
      Term  -- ^ Uniqueness attribute
  | Attr Type Term
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

data AttrLit
  = UniqueAttr
  | SharedAttr
  deriving (Show, Eq)

instance Ord AttrLit where
  SharedAttr <= _ =
    True
  UniqueAttr <= UniqueAttr =
    True
  _ <= _ =
    False

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
  pprint (Type i u) =
    "(" ++ "Type " ++ show i ++ " " ++ show u ++ ")"
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
  pprint x =
    show x

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

data Def
  = PatternMatchingDef
      String  -- ^ name
      [(Term, Term)]  -- ^ equations
      Type  -- ^ type
      Flags
  | TypeDef
      String  -- ^ name
      Type  -- ^ type
      [(String, Term)]  -- ^ constructors
  | ExternDef String Type Flags
  deriving Show

instance Definition Def where
  getNames (PatternMatchingDef n _ _ _) =
    [n]
  getNames (TypeDef n _ conss) =
    n : map fst conss
  getNames (ExternDef name _ _) =
    [name]

data Pattern
  = Binding String
  | Inaccessible Term
  | NumPat Int
  | Constructor String
  | PatApp Pattern Pattern
  deriving Show

newtype Flags =
  Flags
    Bool  -- ^ total
  deriving Show

instance Eq DeBrujnizedTerm where
  DBLoc _ t == t' =
    t == t'
  t == DBLoc _ t' =
    t == t'
  DBBound x == DBBound y =
    x == y
  DBFree x == DBFree y =
    x == y
  DBGlobal v == DBGlobal w =
    v == w
  DBBaseType i == DBBaseType j =
    i == j
  DBUniquenessAttr == DBUniquenessAttr =
    True
  DBAttrLit u == DBAttrLit v =
    u == v
  DBType i u == DBType j v =
    i == j && u == v
  DBAttr ty u == DBAttr ty' v =
    ty == ty' && u == v
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
  | DBMeta String
  | DBGlobal String
  | DBBaseType Int
  | DBUniquenessAttr
  | DBAttrLit AttrLit
  | DBType
      Int  -- ^ universe
      DeBrujnizedTerm  -- ^ Uniqueness attribute
  | DBAttr DeBrujnizedTerm DeBrujnizedTerm
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
    deBruijnize' _ (Meta v) =
      DBMeta v
    deBruijnize' _ (Global v) =
      DBGlobal v
    deBruijnize' _ (BaseType i) =
      DBBaseType i
    deBruijnize' _ UniquenessAttr =
      DBUniquenessAttr
    deBruijnize' _ (AttrLit u) =
      DBAttrLit u
    deBruijnize' vars (Pi n t t') =
      DBPi (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      DBLam (deBruijnize' (n : vars) t)
    deBruijnize' vars (Type i u) =
      DBType i $ deBruijnize' vars u
    deBruijnize' vars (Attr ty u) =
      DBAttr (deBruijnize' vars ty) (deBruijnize' vars u)
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
