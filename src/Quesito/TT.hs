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
  , eq
  , Equality(..)
  )
  where

import Prelude hiding (print, and)

import Quesito
import Quesito.Env (Definition(..))

data Term
  = Local String
  | Hole
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
  deriving (Show, Eq)

data UnOp = Not
  deriving (Show, Eq)

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

data DeBrujnizedTerm
  = DBBound Int
  | DBFree String
  | DBHole
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
    deBruijnize' _ (Hole) =
      DBHole
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

data Equality = AlphaEquivalence | AlphaEquivalenceModuloMetaVariables | Unequal
  deriving Eq

and :: Equality -> Equality -> Equality
infixr 3 `and`

AlphaEquivalence `and` AlphaEquivalence =
  AlphaEquivalence
AlphaEquivalence `and` AlphaEquivalenceModuloMetaVariables =
  AlphaEquivalenceModuloMetaVariables
AlphaEquivalenceModuloMetaVariables `and` AlphaEquivalence =
  AlphaEquivalenceModuloMetaVariables
AlphaEquivalenceModuloMetaVariables `and` AlphaEquivalenceModuloMetaVariables =
  AlphaEquivalenceModuloMetaVariables
Unequal `and` _ =
  Unequal
_ `and` Unequal =
  Unequal

(===) :: Eq a => a -> a -> Equality
infix 4 ===
x === y =
  if x == y then
    AlphaEquivalence
  else
    Unequal

eq :: DeBrujnizedTerm -> DeBrujnizedTerm -> Equality
infix 4 `eq`
DBLoc _ t `eq` t' =
  t `eq` t'
t `eq` DBLoc _ t' =
  t `eq` t'
DBBound x `eq` DBBound y =
  x === y
DBFree x `eq` DBFree y =
  x === y
DBHole `eq` _ =
  AlphaEquivalenceModuloMetaVariables
_ `eq` DBHole =
  AlphaEquivalenceModuloMetaVariables
DBGlobal v `eq` DBGlobal w =
  v === w
DBBaseType i `eq` DBBaseType j =
  i === j
DBUniquenessAttr `eq` DBUniquenessAttr =
  AlphaEquivalence
DBAttrLit u `eq` DBAttrLit v =
  u === v
DBType i u `eq` DBType j v =
  i === j `and` u `eq` v
DBAttr ty u `eq` DBAttr ty' v =
  ty `eq` ty' `and` u `eq` v
DBBytesType n `eq` DBBytesType m =
  n === m
DBNum x `eq` DBNum y =
  x === y
DBPi s s' `eq` DBPi t t' =
  s `eq` t `and` s' `eq` t'
DBApp s s' `eq` DBApp t t' =
  s `eq` t `and` s' `eq` t'
DBAnn s sty `eq` DBAnn t tty =
  s `eq` t `and` sty `eq` tty
_ `eq` _ =
  Unequal
