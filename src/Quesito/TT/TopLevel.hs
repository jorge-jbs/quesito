module Quesito.TT.TopLevel where

import qualified Data.Map as Map

import Quesito
import Quesito.TT hiding (Env)
import Quesito.TT.Eval hiding (Def)
import qualified Quesito.TT.Eval as Eval
import Quesito.TT.TypeAnn
import qualified Quesito.Ann as Ann
import qualified Quesito.LC as LC
import qualified Quesito.LC.TopLevel as LC

import Control.Monad (when)

getNames :: Def -> [String]
getNames (PatternMatchingDef name _ _ _) =
  [name]
getNames (TypeDef name _ conss) =
  name : map fst conss

convertDef :: MonadQues m => Env -> Def -> m (LC.Def, Env)
convertDef = undefined
{-
convertDef env (PatternMatchingDef name equations ty flags) = do
  tell ("Checking pattern matching function declaration " ++ name)
  (tyTy, annTy) <- typeInfAnn env [] ty
  when
    (case tyTy of VType _ -> False; _ -> True)
    (throwError (name ++ "'s type is not of kind type."))
  (args, retTy) <- flattenTy annTy
  ty' <- eval (Map.map fst env) [] ty
  lhssAnn <- mapM (typeInfAnn' (def { inferVars = True }) (Map.insert name (DMatchFunction Nothing ty' flags, annTy) env) []) (map fst equations)
  checkedVars <- mapM (findVars . snd) lhssAnn
  lhss' <- mapM
    (\(vars', (lhs, _)) ->
      mapM (rawToMatch (map (\(x, _, _) -> x) vars') True) (tail $ flattenApp lhs)
    )
    (zip checkedVars equations)
  let evaledEquations =
        map
          (uncurry (evalEquation (DMatchFunction (Just evaledEquations) ty' flags)))
          (zip lhss' (map snd equations))
      env' =
        Map.insert name (DMatchFunction (Just evaledEquations) ty' flags, annTy) env
  equations' <- mapM
    (\(vars', (lhsTy, lhsAnn), (_, rhs)) -> checkEquation env' vars' lhsTy lhsAnn rhs)
    (zip3 checkedVars lhssAnn equations)
  return (LC.PatternMatchingDef name equations' args retTy flags, env')
  where
    flattenTy
      :: MonadQues m
      => Ann.Term
      -> m ([LC.Type], LC.Type)
    flattenTy =
      flatten
      where
        flatten (Ann.Loc _ t) =
          flatten t
        flatten (Ann.Pi _ arg args) = do
          arg' <- LC.cnvType arg
          (args', retTy') <- flatten args
          return (arg' : args', retTy')
        flatten t = do
          t' <- LC.cnvType t
          return ([], t')

    findVars :: MonadQues m => Ann.Term -> m [(String, Value, Ann.Term)]
    findVars (Ann.Local v varTy) = do
      varTy' <- eval (Map.map fst env) [] (Ann.downgrade varTy)
      return [(v, varTy', varTy)]
    findVars (Ann.App s _ t _) =
      (++) <$> findVars s <*> findVars t
    findVars _ =
      return []

    rawToMatch :: MonadQues m => [String] -> Bool -> Term -> m Pattern
    rawToMatch vars normalized (Local x)
      | elem x vars =
        return (Binding x)
      | otherwise =
        case lookupEnv x env of
          Just (TypeDef n _ _, _) | x == n ->
            return (Constructor x)
          Just _ | not normalized ->
            return (Inaccessible (Local x))
          _ -> do
            loc <- getLocation
            throwError ("Free variable at " ++ pprint loc ++ ".")
    rawToMatch vars normalized (Global x) =
      rawToMatch vars normalized (Local x)
    rawToMatch vars _ (App l r) = do
      l' <- rawToMatch vars True l
      r' <- rawToMatch vars False r
      return (MatchApp l' r')
    rawToMatch _ _ (Num x) = do
      return (NumPat x)
    rawToMatch _ _ (BinOp _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
    rawToMatch _ _ (UnOp _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
    rawToMatch _ _ (Type _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type universes (at " ++ pprint loc ++ ")")
    rawToMatch _ _ (BytesType _) = do
      loc <- getLocation
      throwError ("Can't pattern match on bytes types (at " ++ pprint loc ++ ")")
    rawToMatch _ _ (Pi _ _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on function spaces (at " ++ pprint loc ++ ")")
    rawToMatch _ _ (Ann _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type annotations (at " ++ pprint loc ++ ")")
    rawToMatch _ _ (Lam _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on lambda expressions (at " ++ pprint loc ++ ")")
    rawToMatch vars normalized (Loc loc t) =
      rawToMatch vars normalized t `locatedAt` loc

    termToPattern :: MonadQues m => [String] -> Ann.Term -> m LC.Pattern
    termToPattern vars (Ann.Local x _)
      | elem x vars =
        return (LC.Binding x)
      | otherwise = do
        loc <- getLocation
        throwError ("Free variable at " ++ pprint loc ++ ".")
    termToPattern _ (Ann.Global x _) =
      return (LC.Constructor x [])
    termToPattern _ (Ann.App _ _ _ _) = do
      undefined
    termToPattern _ (Ann.Num x b) = do
      return (LC.NumPat x b)
    termToPattern _ (Ann.BinOp _) = do
      loc <- getLocation
      throwError ("Can't pattern match on built-in operations (at " ++ pprint loc ++ ")")
    termToPattern _ (Ann.UnOp _) = do
      loc <- getLocation
      throwError ("Can't pattern match on built-in operations (at " ++ pprint loc ++ ")")
    termToPattern _ (Ann.Type _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type universes (at " ++ pprint loc ++ ")")
    termToPattern _ (Ann.BytesType _) = do
      loc <- getLocation
      throwError ("Can't pattern match on bytes types (at " ++ pprint loc ++ ")")
    termToPattern _ (Ann.Pi _ _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on function spaces (at " ++ pprint loc ++ ")")
    termToPattern _ (Ann.Lam _ _ _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on lambda expressions (at " ++ pprint loc ++ ")")
    termToPattern vars (Ann.Loc loc t) =
      termToPattern vars t `locatedAt` loc

    checkEquation
      :: MonadQues m
      => Env
      -> [(String, Value, Ann.Term)]
      -> Value
      -> Ann.Term
      -> Term
      -> m ([(String, LC.Type)], [LC.Pattern], LC.Term)
    checkEquation env' vars lhsTy lhsAnn rhs = do
      tell ("Checking vars of " ++ name)
      vars' <- mapM (\(x, _, annVarTy) -> (,) x <$> LC.cnvType annVarTy) vars
      tell ("Checking lhs of one of the equations of " ++ name ++ "; ctx: " ++ (show $ name : map (\(name', _, _) -> name') vars))
      ps <- mapM (termToPattern (map (\(x, _, _) -> x) vars)) (tail (Ann.flattenApp lhsAnn))
      tell ("Checking rhs of one of the equations of " ++ name ++ "; ctx: " ++ (show $ name : map (\(name', _, _) -> name') vars))
      (rhsAnn, _) <- typeCheckAnn env' vars rhs lhsTy
      tell ("Converting rhs to LC")
      rhsLc <- LC.cnvBody rhsAnn
      tell ("Successful")
      return (vars', ps, rhsLc)

    evalEquation :: Def -> [Pattern] -> Term -> ([Pattern], Term, Map.Map String Def)
    evalEquation recur lhs' rhs =
      (lhs', rhs, Map.insert name recur (Map.map fst env))
convertDef env (TypeDef name ty conss) = do
  (_, _) <- typeInfAnn env [] ty
  ty' <- eval (Map.map fst env) [] ty
  when
    (case ty' of VType 0 -> False; _ -> True)
    (throwError "Type definitions should be of ground types.")
  let env' = Map.insert name (DDataType ty', Ann.Type 1) env
  conss' <- mapM
      (\(consName, consTy) -> do
        tell ("Holi: " ++ show consTy)
        (_, consTyAnn) <- typeInfAnn env' [] consTy
        tell ("De camino: " ++ show consTyAnn)
        consTy' <- LC.cnvType consTyAnn
        tell ("Terminé")
        return (consName, consTy', consTyAnn)
      )
      conss
  conss'' <- Map.fromList <$> mapM
    (\((consName, consTy), (_, _, consTyAnn)) -> do
      consTy' <- eval (Map.map fst env') [] consTy
      return (consName, (DDataCons consTy', consTyAnn))
    )
    (zip conss conss')
  return (LC.TypeDef name (map (\(x, y, _) -> (x, y)) conss'), Map.union conss'' env')
-}
