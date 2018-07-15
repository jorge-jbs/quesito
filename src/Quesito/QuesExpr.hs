module Quesito.QuesExpr where

import Data.List (delete, nub)

import Quesito.Constant
import Quesito.Type

data QuesExpr
  = Var Char
  | Constant Constant
  | Lambda Char Ty QuesExpr
  | App QuesExpr QuesExpr
  deriving (Eq, Show)

freeVars :: QuesExpr -> [Char]
freeVars (Var v) = [v]
freeVars (Constant _) = []
freeVars (Lambda v _ t) = delete v (freeVars t)
freeVars (App t t') = nub (freeVars t ++ freeVars t')
