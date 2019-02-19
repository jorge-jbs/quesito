module Quesito.LC.TopLevel where

import Quesito.LC
import Quesito.TT.Eval (Flags)

data Pattern
  = Binding String
  | NumPat
      Int -- ^ literal
      Int -- ^ size in bytes
  | Constructor String [Pattern]
  deriving Show

data Def
  = PatternMatchingDecl
      String  -- ^ name
      [([(String, Type)], [Pattern], Term)]  -- ^ equations
      [Type]  -- ^ arguments types
      Type  -- ^ return type
      Flags
  | TypeDecl
      String  -- ^ name
      [(String, Type)]  -- ^ constructors
  deriving Show
