{-# LANGUAGE
  FlexibleContexts
#-}
module Quesito.Ann.Unify where

import Quesito
import Quesito.Ann
import Quesito.Ann.UnifyM
import Quesito.TT (deBruijnize, eq, Equality(..))
import Quesito.Marked.Mark (unmark)

unify
  :: MonadGenProblems Term m
  => Term -> Term
  -> m Bool
unify r s = do
  let equal = do
        let tyR = typeInf r
            tyS = typeInf s
        addProblem $ EQN r tyR s tyS
        return True
  case (deBruijnize (unmark (downgrade r))
      `eq` deBruijnize (unmark (downgrade s))) of
    AlphaEquivalence ->
      equal
    AlphaEquivalenceModuloMetaVariables ->
      equal
    Unequal ->
      return False
