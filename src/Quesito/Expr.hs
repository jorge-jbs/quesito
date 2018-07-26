module Quesito.Expr where

import Data.List (delete, nub, find)

import Quesito.Constant
import Quesito.Type

data Expr a
  = Var a
  | Constant Constant
  | Lambda Var Type (Expr a)
  | App (Expr a) (Expr a)
  | Let (Var, Type, (Expr a)) (Expr a)
  deriving (Eq, Show)

type QuesExpr = Expr Var

type Var = String

freeVars :: QuesExpr -> [Var]
freeVars (Var v) = [v]
freeVars (Constant _) = []
freeVars (Lambda v _ t) = delete v (freeVars t)
freeVars (App t t') = nub (freeVars t ++ freeVars t')
freeVars (Let (v, _, t) t') = nub (freeVars t ++ delete v (freeVars t'))

annotate :: QuesExpr -> Maybe (Expr (Var, Type))
annotate = annotate' []
  where
    annotate' :: [(Var, Type)] -> QuesExpr -> Maybe (Expr (Var, Type))
    annotate' scope (Var v) = Var <$> find (\(v', _) -> v == v') scope
    annotate' _     (Constant c) = Just (Constant c)
    annotate' scope (Lambda v ty t) = Lambda v ty <$> annotate' ((v, ty) : scope) t
    annotate' scope (App t t') = do
      t'' <- annotate' scope t
      t''' <- annotate' scope t'
      return (App t'' t''')
    annotate' scope (Let (v, ty, t) t') = do
      t'' <- annotate' scope t
      t''' <- annotate' ((v, ty) : scope) t'
      return (Let (v, ty, t'') t''')
