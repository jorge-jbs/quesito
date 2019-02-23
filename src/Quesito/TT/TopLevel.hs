module Quesito.TT.TopLevel where

import Control.Monad (when)
import Data.Default

import Quesito
import Quesito.TT
import Quesito.TT.TypeAnn as TypeAnn
import Quesito.Ann.Eval as Eval
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env

getNames :: Def -> [String]
getNames (PatternMatchingDef name _ _ _) =
  [name]
getNames (TypeDef name _ conss) =
  name : map fst conss

typeAnn :: MonadQues m => TypeAnn.Env -> Def -> m Ann.Def
typeAnn env (PatternMatchingDef name equations ty flags) = do
  (tyTy, ty') <- typeInfAnn env [] ty
  when (not $ isType tyTy) (throwError ("The kind of " ++ name ++ " is not Type."))
  equations' <- mapM (\(lhs, rhs) -> typeAnnEquation ty' lhs rhs) equations
  return (Ann.PatternMatchingDef name equations' ty' flags)
  where
    typeAnnEquation :: MonadQues m => Ann.Term -> Term -> Term -> m ([(String, Ann.Type)], [Ann.Pattern], Ann.Term)
    typeAnnEquation ty' lhs rhs = do
      case flattenApp lhs of
        Global name' : _ | name == name' ->
          return ()
        _ ->
          throwError ("Left hand side of equation (" ++ name ++ ") malformed")
      let env' = Env.insert (Ann.PatternMatchingDef name [] ty' (Flags False)) env
      (lhsTy, lhs') <- typeInfAnn' (def { inferVars = True }) env' [] lhs
      pats <- mapM termToPattern (tail $ flattenApp lhs)
      let vars = findVars lhs'
      (rhs', _) <- typeCheckAnn env' [] rhs lhsTy
      return (vars, pats, rhs')

    findVars :: Ann.Term -> [(String, Ann.Type)]
    findVars (Ann.Local v varTy) = do
      [(v, varTy)]
    findVars (Ann.App s t) =
      findVars s ++ findVars t
    findVars _ =
      []

    termToPattern :: MonadQues m => Term -> m Ann.Pattern
    termToPattern (Local x) =
      return (Ann.Binding x)
    termToPattern (Global x) =
      case Env.lookup x env of
        Just (Ann.TypeDef _ _ conss) | x `elem` map fst conss ->
          return (Ann.Constructor x)
        _ -> do
          loc <- getLocation
          throwError ("Free variable at " ++ pprint loc ++ ".")
    termToPattern (App l r) = do
      l' <- termToPattern l
      r' <- termToPattern r
      return (Ann.PatApp l' r')
    termToPattern (Num x) =
      return (Ann.NumPat x)
    termToPattern (BinOp _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
    termToPattern (UnOp _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
    termToPattern (Type _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type universes (at " ++ pprint loc ++ ")")
    termToPattern (BytesType _) = do
      loc <- getLocation
      throwError ("Can't pattern match on bytes types (at " ++ pprint loc ++ ")")
    termToPattern (Pi _ _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on function spaces (at " ++ pprint loc ++ ")")
    termToPattern (Ann _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type annotations (at " ++ pprint loc ++ ")")
    termToPattern (Lam _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on lambda expressions (at " ++ pprint loc ++ ")")
    termToPattern (Loc loc t) =
      termToPattern t `locatedAt` loc
typeAnn env (TypeDef name ty conss) = do
  (tyTy, ty') <- typeInfAnn env [] ty
  when (not $ isType tyTy) (throwError ("The kind of " ++ name ++ " is not Type."))
  conss' <- flip mapM conss (\(name', t) -> do
      (tTy, t') <- typeInfAnn (Env.insert (Ann.TypeDef name ty' []) env) [] t
      when (not $ isType tTy) (throwError ("The kind of " ++ name' ++ " is not Type."))
      return (name', t')
    )
  return (Ann.TypeDef name ty' conss')
