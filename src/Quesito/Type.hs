module Quesito.Type where

data BaseTy
  = Nat
  deriving (Eq, Show)

data Ty
  = BaseTy BaseTy
  | Arrow Ty Ty
  deriving (Eq, Show)
