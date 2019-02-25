module Quesito.LC.TopLevel where

import Quesito.LC
import Quesito.TT (Flags)
import qualified Quesito.Env as Env

type Env = Env.Env Def

data Pattern
  = Binding String
  | NumPat
      Int -- ^ literal
      Int -- ^ size in bytes
  | Constructor String [Pattern]
  deriving Show

data Def
  = PatternMatchingDef
      String  -- ^ name
      [([(String, Type)], [Pattern], Term)]  -- ^ equations
      [Type]  -- ^ arguments types
      Type  -- ^ return type
      Flags
  | TypeDef
      String  -- ^ name
      [(String, Type)]  -- ^ constructors
  deriving Show
