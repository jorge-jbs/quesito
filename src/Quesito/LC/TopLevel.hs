module Quesito.LC.TopLevel where

import Quesito
import Quesito.LC

data Decl
  = ExprDecl
      { name :: Name
      , args :: [(Name, Type Name)]
      , body :: Term Name
      , retTy :: Type Name
      }
  | TypeDecl
      { name :: Name
      , constructors :: [(Name, Type Name)]
      }
  deriving Show
