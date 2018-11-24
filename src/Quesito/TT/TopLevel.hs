module Quesito.TT.TopLevel where

import Quesito
import Quesito.TT
import Quesito.TT.Eval
import Quesito.TT.TypeCheck

import Data.Foldable (foldlM)
import Data.List (find)
import Control.Monad (when)

data Decl
  = ExprDecl Name (Term Name) (Term Name)
  -- | MatchFunctionDecl Name [([(Name, Term Name)], Term Name, Term Name)] (Term Name)

checkDecl :: [(Name, Def Value Value)] -> Decl -> Ques [(Name, Def Value Value)]
checkDecl env (ExprDecl name expr ty) = do
  tell ["Checking expression declaration " ++ name]
  tyTy <-
    typeInf env [] ty `catchError`
      \err -> throwError ("Type error while checking " ++ name ++ ": " ++ err)

  case tyTy of
    VType _ -> do
      ty' <- eval env [] ty
      typeCheck ((name, DExpr undefined ty') : env) [] (subst name (Free name) expr) ty'
      expr' <- evalRecursive ty'
      return [(name, DExpr expr' ty')]
    _ ->
      throwError (name ++ "'s type is not of kind Type.")
  where
    evalRecursive :: Value -> Ques Value
    evalRecursive ty' = do
      tell ["Recurring on " ++ name]
      expr' <- evalRecursive ty'
      tell ["Finished recurring on " ++ name]
      eval ((name, DExpr expr' ty') : env) [] expr

{-
checkDecl env (MatchFunctionDecl name equations ty) = do
  tell ["Checking pattern matching function declaration " ++ name]
  typeCheck env [] ty (VType 1000)
  ty' <- eval env [] ty
  checkedVars <- mapM (\(vars, _, _) -> checkVars vars) equations
  mapM_ (\(vars', (_, rhs, lhs)) -> checkEquation vars' rhs lhs ty') (zip checkedVars equations)
  lhss' <- mapM (\(vars', lhs) -> mapM (rawToMatch (map fst vars') True) (tail $ flattenApp lhs)) (zip checkedVars (map (\(_, x, _) -> x) equations))
  let evaledEquations = map (uncurry $ evalEquation (DMatchFunction evaledEquations ty')) (zip lhss' (map (\(_, _, x) -> x) equations))
  return [(name, DMatchFunction evaledEquations ty')]
  where
    checkVars :: [(Name, Term Name)] -> Ques [(Name, Value)]
    checkVars vars =
      foldlM
        (\vars' (name', ty') -> do
          let freedTy' = freeVars (map fst vars') ty'
          tyTy' <- typeInf env vars' freedTy'
          when
            (case tyTy' of VType _ -> False; _ -> True)
            (throwError (name' ++ " variable at function declaration " ++ name ++ " is not of kind Type."))
          freedTy'' <- eval env [] freedTy'
          return ((name', freedTy'') : vars')
        )
        []
        vars

    flattenApp :: Term Name -> [Term Name]
    flattenApp =
      flattenApp' []
      where
        flattenApp' :: [Term Name] -> Term Name -> [Term Name]
        flattenApp' as (App f a) =
          flattenApp' (a:as) f
        flattenApp' as (Loc _ a) =
          flattenApp' as a
        flattenApp' as f =
          f:as

    rawToMatch :: [Name] -> Bool -> Term Name -> Ques (Pattern Name)
    rawToMatch vars normalized (Bound x)
      | elem x vars =
        return (Binding x)
      | otherwise =
        case find ((==) x . fst) env of
          Just _ | not normalized ->
            return (Inaccessible (Bound x))
          _ -> do
            loc <- getLocation
            throwError ("Free variable at " ++ show loc ++ ".")
    rawToMatch vars normalized (Free x) =
      rawToMatch vars normalized (Bound x)
    rawToMatch vars _ (App l r) = do
      l' <- rawToMatch vars True l
      r' <- rawToMatch vars False r
      return (MatchApp l' r')
    rawToMatch _ _ (Num x) = do
      return (NumPat x)
    rawToMatch _ _ (Type _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type universes (at " ++ show loc ++ ")")
    rawToMatch _ _ (BytesType _) = do
      loc <- getLocation
      throwError ("Can't pattern match on bytes types (at " ++ show loc ++ ")")
    rawToMatch _ _ (Pi _ _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on function spaces (at " ++ show loc ++ ")")
    rawToMatch _ _ (Ann _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type annotations (at " ++ show loc ++ ")")
    rawToMatch _ _ (Lam _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on lambda expressions (at " ++ show loc ++ ")")
    rawToMatch vars normalized (Loc loc t) =
      rawToMatch vars normalized t `locatedAt` loc

    checkEquation :: [(Name, Value)] -> Term Name -> Term Name -> Value -> Ques ()
    checkEquation vars lhs rhs ty' = do
      let freedLhs = freeVars (name:map fst vars) lhs
      let freedRhs = freeVars (name:map fst vars) rhs
      tell ["Checking lhs of one of the equations of " ++ name]
      lhsTy <- typeInf env ((name, ty') : vars) freedLhs
      tell ["Checking rhs of one of the equations of " ++ name ++ "; ctx: " ++ (show $ map fst ((name, ty') : vars))]
      typeCheck env ((name, ty') : vars) freedRhs lhsTy
      tell ["Successful"]

    evalEquation :: Def Value Value -> [Pattern Name] -> Term Name -> ([Pattern Name], [(Name, Value)] -> Ques Value)
    evalEquation recur lhs' rhs =
      (lhs', \ctx -> eval ((name, recur):env) ctx rhs)
-}
