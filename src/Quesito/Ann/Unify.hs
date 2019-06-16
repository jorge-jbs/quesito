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
        addProblem $ EQN r s
        return True
  case (deBruijnize (unmark (downgrade r))
      `eq` deBruijnize (unmark (downgrade s))) of
    AlphaEquivalence ->
      equal
    AlphaEquivalenceModuloMetaVariables ->
      equal
    Unequal ->
      return False

simplify
  :: (MonadExcept m)
  => Problem Term -> m [Problem Term]
simplify (EQN (Local x xTy _) (Local y yTy _)) =
  if x == y then
    simplify $ EQN xTy yTy
  else
    throwError ("Unification error: " ++ x ++ " /= " ++ y)
simplify (EQN (Global x xTy) (Global y yTy)) =
  if x == y then
    simplify $ EQN xTy yTy
  else
    throwError ("Unification error: " ++ x ++ " /= " ++ y)
simplify (EQN (BaseType i) (BaseType j)) =
  if i == j then
    return []
  else
    throwError ("Unification error: " ++ show i ++ " /= " ++ show j)
simplify (EQN UniquenessAttr UniquenessAttr) =
  return []
simplify (EQN (AttrLit u) (AttrLit v)) =
  if u == v then
    return []
  else
    throwError ("Unification error: " ++ show u ++ " /= " ++ show v)
simplify (EQN (BytesType i) (BytesType j)) =
  if i == j then
    return []
  else
    throwError ("Unification error: " ++ show i ++ " /= " ++ show j)
simplify (EQN (Type i u) (Type j v)) =
  if i == j then
    simplify $ EQN u v
  else
    throwError ("Unification error: " ++ show i ++ " /= " ++ show j)
simplify (EQN (Attr ty1 u) (Attr ty2 v)) =
  (++) <$> simplify (EQN ty1 ty2) <*> simplify (EQN u v)
simplify (EQN (BinOp op1) (BinOp op2)) =
  if op1 == op2 then
    return []
  else
    throwError ("Unification error: " ++ show op1 ++ " /= " ++ show op2)
simplify (EQN (UnOp op1) (UnOp op2)) =
  if op1 == op2 then
    return []
  else
    throwError ("Unification error: " ++ show op1 ++ " /= " ++ show op2)
simplify (EQN (Num n nB) (Num m mB)) =
  if n == m && nB == mB then
    return []
  else
    throwError ("Unification error: " ++ show n ++ " /= " ++ show m)
simplify (EQN (Pi x ty1 ty2) (Pi y ty1' ty2')) =
  (++)
    <$> simplify (EQN ty1 ty1')
    <*> undefined -- EQN ty2 ty2'  -- TODO: Should substitute x in ty2 and y in ty2'
simplify (EQN (App r s) (App r' s')) =
  (++) <$> simplify (EQN r r') <*> simplify (EQN s s')
simplify (EQN (Lam x _ r) (Lam y _ s)) =
  undefined -- EQN r s  -- TODO: Should substitute x in r and y in s
simplify p =
  return [p]

solveProblem :: (MonadExcept m) => Problem Term -> m (Subs Term)
solveProblem (EQN (Hole i _) t) =
  return [(i, t)]
solveProblem (EQN t (Hole i _)) =
  return [(i, t)]
solveProblem (EQN r s) =
  if (deBruijnize (unmark (downgrade r))
      `eq` deBruijnize (unmark (downgrade s))) == AlphaEquivalence then
    return []
  else
    throwError ("Not enough information to unify " ++ show r ++ " with " ++ show s)

solve
  :: (MonadExcept m)
  => [Problem Term] -> m (Subs Term)
solve = \ps -> (concat <$> mapM simplify ps) >>= solve'
  where
    solve' :: (MonadExcept m) => [Problem Term] -> m (Subs Term)
    solve' [] =
      return []
    solve' (p:ps) = do
      subs <- solveProblem p
      let ps' =
            map (\(EQN r s) -> EQN (substHoles subs r) (substHoles subs s)) ps
      (++) subs <$> solve' ps'
