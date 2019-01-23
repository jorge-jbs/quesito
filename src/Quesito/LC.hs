module Quesito.LC where

import Quesito
import qualified Quesito.Ann as Ann

type Name = String

data Term v
  = Local v (GType v)
  | Global Name (GType v)
  | Lit { num :: Int, bytes :: Int }
  | App v (Type v) [Term v]
  deriving Show

data GType v
  = BytesType Int
  | TypeVar v
  deriving Show

data Type v
  = GroundType (GType v)
  | Pi Name (GType v) (Type v)
  deriving Show

cnvBody :: Ann.Term Ann.Name -> Ques (Term Name)
cnvBody (Ann.Local v ty) =
  Local v <$> cnvGType ty
cnvBody (Ann.Global v ty) =
  Global v <$> cnvGType ty
cnvBody (Ann.Type _) =
  throwError "WIP" -- return (GType (Type lvl))
cnvBody (Ann.BytesType _) =
  throwError "WIP 2" -- return (GType (BytesType n))
cnvBody (Ann.Num n bytes') =
  return (Lit n bytes')
cnvBody (Ann.Pi _ _ _) =
  throwError "Can't convert Pi type to a Lambda-Calculus expression"
cnvBody t@(Ann.App _ _) =
  case headAndArgs t of
    (Ann.Global v ty, args) ->
      App v <$> cnvType ty <*> mapM cnvBody args
    _ -> do
      loc <- getLocation
      throwError ("Application to expression instead of free variable at " ++ pprint loc)
  where
    headAndArgs :: Ann.Term Ann.Name -> (Ann.Term Ann.Name, [Ann.Term Ann.Name])
    headAndArgs =
      headAndArgs' []
      where
        headAndArgs' args (Ann.App (Ann.Ann t' _) (Ann.Ann arg _)) =
          headAndArgs' (arg : args) t'
        headAndArgs' args (Ann.Loc _ t') =
          headAndArgs' args t'
        headAndArgs' args t' =
          (t', args)
cnvBody (Ann.Lam _ _ _) =
  throwError "Can't convert Lambda expresson to a Lambda-Calculus expression"
cnvBody (Ann.Loc _ t) =
  cnvBody t

cnvGType :: Ann.Term Ann.Name -> Ques (GType Name)
cnvGType (Ann.Global v _) =
  return (TypeVar v)
cnvGType (Ann.Type _) =
  throwError "WIP 3" -- return (Type lvl)
cnvGType (Ann.BytesType n) =
  return (BytesType n)
cnvGType (Ann.Loc _ t) =
  cnvGType t
cnvGType _ =
  throwError "Can't convert arbitrary expressions to Lambda-Calculus ground types"

cnvType :: Ann.Term Ann.Name -> Ques (Type Name)
cnvType (Ann.Local _ _) =
  throwError "WIP 5" -- return (TypeVar v)
cnvType (Ann.Global v _) =
  return (GroundType (TypeVar v))
cnvType (Ann.Type _) =
  throwError "WIP 4" -- return (GroundType (Type lvl))
cnvType (Ann.BytesType n) =
  return (GroundType (BytesType n))
cnvType (Ann.Pi v t t') =
  Pi v <$> cnvGType t <*> cnvType t'
cnvType (Ann.Loc _ t) =
  cnvType t
cnvType _ =
  throwError "Can't convert arbitrary expressions to Lambda-Calculus types"
