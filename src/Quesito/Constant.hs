module Quesito.Constant where

import Quesito.Type

data Constant
  = Num Int
  | Plus2
  | Plus1 Int
  deriving (Eq, Show)

constType :: Constant -> Type
constType (Quesito.Constant.Num _) = BaseType Nat
constType Plus2 = Arrow (BaseType Nat) (Arrow (BaseType Nat) (BaseType Nat))
constType (Plus1 _) = Arrow (BaseType Nat) (BaseType Nat)
