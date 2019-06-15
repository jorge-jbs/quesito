module Quesito.Marked
  ( Term(..)
  , Type
  )
  where

import Quesito
import Quesito.Env (Definition(..))
import Quesito.TT (AttrLit(..), BinOp(..), UnOp(..), Flags)

data Term
  = Local String AttrLit
  | Meta String
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
