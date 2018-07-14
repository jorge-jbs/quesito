module Quesito.Term where

import Data.List (delete, nub)

import Quesito.Constant
import Quesito.Type

data Term
  = Var Char (Maybe Ty)
  | Constant Constant
  | Lambda Char Ty Term
  | App Term Term
  deriving (Eq, Show)

freeVars :: Term -> [Char]
freeVars (Var v _) = [v]
freeVars (Constant _) = []
freeVars (Lambda v _ t) = delete v (freeVars t)
freeVars (App t t') = nub (freeVars t ++ freeVars t')
