module Quesito.Expr where

import Data.List (delete, nub)

import Quesito.Constant
import Quesito.Type

data Expr a
  = Var a
  | Constant Constant
  | Lambda a Type (Expr a)
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
