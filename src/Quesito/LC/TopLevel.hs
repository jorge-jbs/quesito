module Quesito.LC.TopLevel where

import Quesito.LC
import Quesito.TT.Eval (Flags)

data Pattern name
  = Binding name
  | NumPat { num :: Int, bytes :: Int }
  | Constructor name [Pattern name]
  deriving Show

data Decl
  = PatternMatchingDecl
      { name :: Name
      , equations :: [([(Name, Type Name)], [Pattern Name], Term Name)]
      , args_ :: [Type Name]
      , retTy :: Type Name
      , flags :: Flags
      }
  | TypeDecl
      { name :: Name
      , constructors :: [(Name, Type Name)]
      }
  deriving Show
