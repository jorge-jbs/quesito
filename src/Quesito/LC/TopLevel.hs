module Quesito.LC.TopLevel where

import Quesito.LC
import Quesito.TT.Eval (Flags)

data Pattern
  = Binding String
  | NumPat { num :: Int, bytes :: Int }
  | Constructor String [Pattern]
  deriving Show

data Decl
  = PatternMatchingDecl
      { name :: String
      , equations :: [([(String, Type)], [Pattern], Term)]
      , args_ :: [Type]
      , retTy :: Type
      , flags :: Flags
      }
  | TypeDecl
      { name :: String
      , constructors :: [(String, Type)]
      }
  deriving Show
