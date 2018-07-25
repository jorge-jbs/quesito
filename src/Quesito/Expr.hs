module Quesito.Expr where

import Data.List (delete, nub)

import Quesito.Constant
import Quesito.Type

data Expr a
  = Var a
  | Constant Constant
  | Lambda a Ty (Expr a)
  | App (Expr a) (Expr a)
  deriving (Eq, Show)

type QuesExpr = Expr Char

freeVars :: QuesExpr -> [Char]
freeVars (Var v) = [v]
freeVars (Constant _) = []
freeVars (Lambda v _ t) = delete v (freeVars t)
freeVars (App t t') = nub (freeVars t ++ freeVars t')
