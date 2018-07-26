module Quesito.Type where

data BaseType
  = Nat
  deriving (Eq, Show)

data Type
  = BaseType BaseType
  | Arrow Type Type
  | Prod Type Type
  deriving (Eq, Show)
