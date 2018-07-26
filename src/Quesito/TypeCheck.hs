module Quesito.TypeCheck (typeCheck) where

import Quesito.Expr
import Quesito.Type
import Quesito.Constant

typeCheck :: Expr (Var, Type) -> Maybe Type
typeCheck (Var (_, ty)) = Just ty
typeCheck (Constant c) = Just (constType c)
typeCheck (Lambda _ ty t) = Arrow ty <$> typeCheck t
typeCheck (App t t') = do
  ty <- typeCheck t
  ty' <- typeCheck t'
  case (ty, ty') of
    (Arrow x y, z) | x == z -> Just y
    _ -> Nothing
typeCheck (Let (_, ty, t) t') = do
  if typeCheck t == Just ty then
    typeCheck t'
  else
    Nothing
