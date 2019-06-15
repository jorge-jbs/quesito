{-# LANGUAGE
  StandaloneDeriving
#-}

module Quesito.Ann.Unify where
  
type Subs t =
  [(String, t)]

data Decl t
  = Hole
  | Defn t

data Entry t
  = MV String t (Decl t)
  | Prob Status (Problem t)

data Status
  = Blocked
  | Active
  deriving Show

data Param t
  = P t
  | Twins t t

type Params t =
  [(String, Param t)]

data Equation t =
  EQN t t t t

data Problem t
  = Unify (Equation t)
  | ForAll String (Param t) (Problem t)

type Context t =
  ([Entry t], [Either (Subs t) (Entry t)])

deriving instance Show t => Show (Decl t)
deriving instance Show t => Show (Entry t)
deriving instance Show t => Show (Param t)
deriving instance Show t => Show (Equation t)
deriving instance Show t => Show (Problem t)
