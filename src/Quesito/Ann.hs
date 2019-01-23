module Quesito.Ann where

import Quesito
import qualified Quesito.TT as TT

type Name = TT.Name

data Term v
  = Local v (Term v)
  | Global Name (Term v)
  | Type Int
  | BytesType Int
  | Num { num :: Int, bytes :: Int }
  | Pi Name (Term v) (Term v)
  | App (Ann Term v) (Ann Term v)
  | Lam TT.Name (Term v) (Ann Term v)
  | Loc Location (Term v)
  deriving Show

data Ann term v = Ann (term v) (term v)
  deriving Show
