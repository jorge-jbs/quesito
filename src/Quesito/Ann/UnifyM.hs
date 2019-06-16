{-# LANGUAGE
  StandaloneDeriving
#-}

module Quesito.Ann.UnifyM where
  
type Subs t =
  [(Int, t)]

data Param t
  = P t
  | Twins t t

data Problem t
  = EQN t t

deriving instance Show t => Show (Param t)
deriving instance Show t => Show (Problem t)
deriving instance Eq t => Eq (Problem t)
