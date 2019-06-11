module Quesito.Marked
  ( Term(..)
  , Type
  , deBruijnize
  )
  where

import Quesito
import Quesito.Env (Definition(..))
import Quesito.TT (AttrLit(..), BinOp(..), UnOp(..), Flags)

data Term
  = Local String AttrLit
  | Global String
  | BaseType Int
  | UniquenessAttr
  | AttrLit AttrLit
  | Type Int Term
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
  deriving Show

instance Definition Def where
  getNames (PatternMatchingDef n _ _ _) =
    [n]
  getNames (TypeDef n _ conss) =
    n : map fst conss

instance Eq DeBrujnizedTerm where
  DBLoc _ t == t' =
    t == t'
  t == DBLoc _ t' =
    t == t'
  DBBound x u == DBBound y v =
    x == y && u == v
  DBFree x u == DBFree y v =
    x == y && u == v
  DBGlobal v == DBGlobal w =
    v == w
  DBType i u == DBType j v =
    i == j && u == v
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
  = DBBound Int AttrLit
  | DBFree String AttrLit
  | DBGlobal String
  | DBType
      Int  -- ^ universe
      DeBrujnizedTerm  -- ^ Uniqueness attribute
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
    deBruijnize' vars (Local v u) =
      case takeWhile (\v' -> v /= v') vars of
        [] ->
          DBFree v u
        xs ->
          DBBound (length xs) u
    deBruijnize' _ (Global v) =
      DBGlobal v
    deBruijnize' vars (Pi n t t') =
      DBPi (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      DBLam (deBruijnize' (n : vars) t)
    deBruijnize' vars (Type i u) =
      DBType i $ deBruijnize' vars u
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
