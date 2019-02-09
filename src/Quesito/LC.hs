module Quesito.LC where

import Quesito
import qualified Quesito.Ann as Ann
import Quesito.TT (BinOp(..), UnOp(..))

data Term
  = Local String GType
  | Global String GType
  | Lit { num :: Int, bytes :: Int }
  | App String Type [Term]
  | BinOp BinOp Term Term
  | UnOp UnOp Term
  deriving Show

data GType
  = BytesType Int
  | TypeVar String
  deriving Show

data Type
  = GroundType GType
  | Pi String GType Type
  deriving Show

cnvBody :: Ann.Term -> Ques Term
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
cnvBody t@(Ann.App _ _ _ _) =
  case headAndArgs t of
    (Ann.Global v ty, args) ->
      App v <$> cnvType ty <*> mapM cnvBody args
    (Ann.BinOp op, [a, b]) ->
      BinOp op <$> cnvBody a <*> cnvBody b
    (Ann.UnOp op, [a]) ->
      UnOp op <$> cnvBody a
    _ -> do
      loc <- getLocation
      throwError ("Application to expression instead of global variable at " ++ pprint loc)
  where
    headAndArgs :: Ann.Term -> (Ann.Term, [Ann.Term])
    headAndArgs =
      headAndArgs' []
      where
        headAndArgs' args (Ann.App t' _ arg _) =
          headAndArgs' (arg : args) t'
        headAndArgs' args (Ann.Loc _ t') =
          headAndArgs' args t'
        headAndArgs' args t' =
          (t', args)
cnvBody (Ann.Lam _ _ _ _) =
  throwError "Can't convert Lambda expression to a Lambda-Calculus expression"
cnvBody (Ann.BinOp _) =
  throwError "Can't convert binary operation  to a Lambda-Calculus expression"
cnvBody (Ann.UnOp _) =
  throwError "Can't convert operation to a Lambda-Calculus expression"
cnvBody (Ann.Loc _ t) =
  cnvBody t

cnvGType :: Ann.Type -> Ques GType
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

cnvType :: Ann.Type -> Ques Type
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
