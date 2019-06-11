{-# LANGUAGE FlexibleContexts #-}
module Quesito.TT.TopLevel where

import Control.Monad (when, forM)
import Data.Default

import Quesito
import Quesito.TT
import Quesito.TT.TypeAnn as TypeAnn
import Quesito.Marked.Mark
import Quesito.Ann.Eval as Eval
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env

getNames :: Def -> [String]
getNames (PatternMatchingDef name _ _ _) =
  [name]
getNames (TypeDef name _ conss) =
  name : map fst conss

termToPattern :: (MonadExcept m, MonadLocatable m) => (String -> Bool) -> Ann.Term -> m Ann.Pattern
termToPattern _ (Ann.Local x ty _) =
  return (Ann.Binding x ty)
termToPattern isCons t@(Ann.Global x _) =
  if isCons x then
    return $ Ann.Constructor x
  else
    return $ Ann.Inaccessible t
termToPattern env t@(Ann.App l r) =
  case Ann.flattenApp t of
    [Ann.BinOp Add, x, Ann.Num y _] -> do
      f x y
    [Ann.BinOp Add, Ann.Num x _, y] ->
      f y x
    _ -> do
      l' <- termToPattern env l
      r' <- termToPattern env r
      return (Ann.PatApp l' r')
  where
    f x 0 =
      termToPattern env x
    f x y =
      Ann.NumSucc <$> f x (y-1)
termToPattern _ (Ann.Num x b) =
  return (Ann.NumPat x b)
termToPattern _ (Ann.BinOp _) = do
  loc <- askLoc
  throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.UnOp _) = do
  loc <- askLoc
  throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.Type _ _) = do
  loc <- askLoc
  throwError ("Can't pattern match on type universes (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.BytesType _) = do
  loc <- askLoc
  throwError ("Can't pattern match on bytes types (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.Pi _ _ _) = do
  loc <- askLoc
  throwError ("Can't pattern match on function spaces (at " ++ pprint loc ++ ")")
termToPattern _ (Ann.Lam _ _ _) = do
  loc <- askLoc
  throwError ("Can't pattern match on lambda expressions (at " ++ pprint loc ++ ")")

typeAnnEquation
  :: (MonadLog m, MonadExcept m, MonadLocatable m)
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
  (lhsTy, lhs') <- typeInfAnn' (def { inferVars = True }) [] (mark lhs) `withEnv` env'
  pats <- mapM (termToPattern (\x -> case Env.lookup x env of
      Just (Ann.TypeDef _ _ conss) | x `elem` map fst conss ->
        True
      _ ->
        False
    )) (tail $ Ann.flattenApp lhs')
  let vars = findVars lhs'
  ctx <- mapM (\(v, vty) -> do vty' <- eval [] vty `withEnv` env; return (v, vty', vty)) vars
  (rhs', _) <- typeCheckAnn ctx (mark rhs) lhsTy `withEnv` env'
  return (vars, pats, rhs')

findVars :: Ann.Term -> [(String, Ann.Type)]
findVars (Ann.Local v varTy _) = do
  [(v, varTy)]
findVars (Ann.App s t) =
  findVars s ++ findVars t
findVars _ =
  []

typeAnn :: (MonadLog m, MonadExcept m, MonadLocatable m) => TypeAnn.Env -> Def -> m Ann.Def
typeAnn env (PatternMatchingDef name equations ty flags) = do
  (tyTy, ty') <- typeInfAnn [] (mark ty) `withEnv` env
  when (not $ isType tyTy) (throwError ("The kind of " ++ name ++ " is not Type."))
  equations' <- mapM (uncurry $ typeAnnEquation env name ty') equations
  return (Ann.PatternMatchingDef name equations' ty' flags)
typeAnn env (TypeDef name ty conss) = do
  (tyTy, ty') <- typeInfAnn [] (mark ty) `withEnv` env
  when (not $ isType tyTy) (throwError ("The kind of " ++ name ++ " is not Type."))
  conss' <- flip mapM conss (\(name', t) -> do
      (tTy, t') <- typeInfAnn [] (mark t) `withEnv` Env.insert (Ann.TypeDef name ty' []) env
      when (not $ isType tTy) (throwError ("The kind of " ++ name' ++ " is not Type."))
      return (name', t')
    )
  return (Ann.TypeDef name ty' conss')
