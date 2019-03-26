module Quesito.TT.TopLevel where

import Control.Monad (when, forM)
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

termToPattern :: MonadQues m => (String -> Bool) -> Ann.Term -> m Ann.Pattern
termToPattern _ (Ann.Local x _) =
  return (Ann.Binding x)
termToPattern isCons t@(Ann.Global x _) =
  if isCons x then
    return $ Ann.Constructor x
  else
    return $ Ann.Inaccessible t
    {-
  else do
    loc <- getLocation
    throwError ("Free variable at " ++ pprint loc ++ ".")
    -}
termToPattern env (Ann.App l r) = do
  l' <- termToPattern env l
  r' <- termToPattern env r
  return (Ann.PatApp l' r')
termToPattern _ (Ann.Num x b) =
  return (Ann.NumPat x b)
termToPattern _ (Ann.BinOp _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.UnOp _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.Type _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type universes (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.BytesType _) = do
  loc <- getLocation
  throwError ("Can't pattern match on bytes types (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.Pi _ _ _) = do
  loc <- getLocation
  throwError ("Can't pattern match on function spaces (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.Lam _ _ _) = do
  loc <- getLocation
  throwError ("Can't pattern match on lambda expressions (at " ++ pprint loc ++ ")")

typeAnnEquation
  :: MonadQues m
  => TypeAnn.Env
  -> String
  -> Ann.Type
  -> Term
  -> Term
  -> m ([(String, Ann.Type)], [Ann.Pattern], Ann.Term)
typeAnnEquation env name ty' lhs rhs = do
  case flattenApp lhs of
    Global name' : _ | name == name' ->
      return ()
    _ ->
      throwError ("Left hand side of equation (" ++ name ++ ") malformed")
  let env' = Env.insert (Ann.PatternMatchingDef name [] ty' (Flags False)) env
  (lhsTy, lhs') <- typeInfAnn' (def { inferVars = True }) env' [] lhs
  pats <- mapM (termToPattern (\x -> case Env.lookup x env of
      Just (Ann.TypeDef _ _ conss) | x `elem` map fst conss ->
        True
      _ ->
        False
    )) (tail $ Ann.flattenApp lhs')
  let vars = findVars lhs'
  ctx <- mapM (\(v, vty) -> do vty' <- eval env [] vty; return (v, vty', vty)) vars
  (rhs', _) <- typeCheckAnn env' ctx rhs lhsTy
  return (vars, pats, rhs')

findVars :: Ann.Term -> [(String, Ann.Type)]
findVars (Ann.Local v varTy) = do
  [(v, varTy)]
findVars (Ann.App s t) =
  findVars s ++ findVars t
findVars _ =
  []

typeAnn :: MonadQues m => TypeAnn.Env -> Def -> m Ann.Def
typeAnn env (PatternMatchingDef name equations ty flags) = do
  (tyTy, ty') <- typeInfAnn env [] ty
  when (not $ isType tyTy) (throwError ("The kind of " ++ name ++ " is not Type."))
  equations' <- mapM (uncurry $ typeAnnEquation env name ty') equations
  return (Ann.PatternMatchingDef name equations' ty' flags)
typeAnn env (TypeDef name ty conss) = do
  (tyTy, ty') <- typeInfAnn env [] ty
  when (not $ isType tyTy) (throwError ("The kind of " ++ name ++ " is not Type."))
  conss' <- flip mapM conss (\(name', t) -> do
      (tTy, t') <- typeInfAnn (Env.insert (Ann.TypeDef name ty' []) env) [] t
      when (not $ isType tTy) (throwError ("The kind of " ++ name' ++ " is not Type."))
      return (name', t')
    )
  return (Ann.TypeDef name ty' conss')
