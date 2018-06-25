module SimplyTypedLambdaCalculus where

import Parse

data BaseTy
  = Nat
  deriving (Eq, Show)

data Ty
  = BaseTy BaseTy
  | Arrow Ty Ty
  deriving (Eq, Show)

data Constant
  = Num Int
  deriving (Eq, Show)

data Term
  = Var Char (Maybe Ty)
  | Constant Constant
  | Lambda Char Ty Term
  | App Term Term
  deriving (Eq, Show)

constType :: Constant -> Ty
constType (SimplyTypedLambdaCalculus.Num _) = BaseTy Nat

typeCheck :: Term -> Maybe Ty
typeCheck (Var _ ty) = ty
typeCheck (Constant c) = Just (constType c)
typeCheck (Lambda v ty t) = do
  ty' <- typeCheck t
  return (Arrow ty ty')
  where
    annotate :: Term -> Term
    annotate (Var v' _) = Var v' (Just ty)
    annotate t@(Lambda v' _ t') =
      if v == v' then
        t
      else
        annotate t'
    annotate (App t t') = App (annotate t) (annotate t')
typeCheck (App t t') = do
  ty <- typeCheck t
  ty' <- typeCheck t'
  case ty of
    Arrow ty1 ty2 | ty1 == ty' -> Just ty2
    _ -> Nothing
