module Quesito.LC.TopLevel where

import Quesito.LC

import Data.List (groupBy)

data Pattern name
  = Binding name
  | NumPat { num :: Int, bytes :: Int }
  | Constructor name [Pattern name]
  deriving Show

data Decl
  = ExprDecl
      { name :: Name
      , args :: [(Name, Type Name)]
      , body :: Term Name
      , retTy :: Type Name
      }
  | PatternMatchingDecl
      { name :: Name
      , equations :: [([(Name, Type Name)], [Pattern Name], Term Name)]
      , args_ :: [Type Name]
      , retTy :: Type Name
      }
  | TypeDecl
      { name :: Name
      , constructors :: [(Name, Type Name)]
      }
  deriving Show
