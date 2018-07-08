module Quesito.Term where

import Quesito.Constant
import Quesito.Type

data Term
  = Var Char (Maybe Ty)
  | Constant Constant
  | Lambda Char Ty Term
  | App Term Term
  deriving (Eq, Show)
