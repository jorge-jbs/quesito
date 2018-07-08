module Quesito.Constant where

import Quesito.Type

data Constant
  = Num Int
  | Plus2
  | Plus1 Int
  deriving (Eq, Show)

constType :: Constant -> Ty
constType (Quesito.Constant.Num _) = BaseTy Nat
constType Plus2 = Arrow (BaseTy Nat) (Arrow (BaseTy Nat) (BaseTy Nat))
constType (Plus1 _) = Arrow (BaseTy Nat) (BaseTy Nat)
