module Quesito.TT.TopLevel where

import Data.Foldable (foldlM)
import Data.List (find)
import qualified Data.Map as Map
import Data.Default

import Quesito
import Quesito.TT
import Quesito.TT.Eval hiding (Env)
import Quesito.TT.TypeAnn
import qualified Quesito.Ann as Ann
import qualified Quesito.LC as LC
import qualified Quesito.LC.TopLevel as LC

import Control.Monad (when)

data Decl
  = PatternMatchingDecl Name [(Term Name, Term Name)] (Term Name) Flags
  | TypeDecl
      Name
      (Term Name)  -- ^ Type
      [(Name, Term Name)]  -- ^ Constructors
  deriving Show

getNames :: Decl -> [Name]
getNames (PatternMatchingDecl name _ _ _) =
  [name]
getNames (TypeDecl name _ conss) =
  name : map fst conss

ttDeclToLcDecl :: Env -> Decl -> Ques (LC.Decl, Env)
ttDeclToLcDecl env (PatternMatchingDecl name equations ty flags) = do
  tell ["Checking pattern matching function declaration " ++ name]
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
    (\(vars', (lhsTy, lhsAnn), (_, rhs)) -> checkEquation env' vars' lhsTy lhsAnn rhs ty')
    (zip3 checkedVars lhssAnn equations)
  return (LC.PatternMatchingDecl name equations' args retTy flags, env')
  where
    flattenTy
      :: Ann.Term Ann.Name
      -> Ques ([LC.Type LC.Name], LC.Type LC.Name)
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

    findVars :: Ann.Term Name -> Ques [(Name, Value, Ann.Term Name)]
    findVars (Ann.Local v ty) = do
      ty' <- eval (Map.map fst env) [] (Ann.downgrade ty)
      return [(v, ty', ty)]
    findVars (Ann.App (Ann.Ann s _) (Ann.Ann t _)) =
      (++) <$> findVars s <*> findVars t
    findVars _ =
      return []

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

    flattenApp' :: Ann.Term Name -> [Ann.Term Name]
    flattenApp' =
      flattenApp'' []
      where
        flattenApp'' :: [Ann.Term Name] -> Ann.Term Name -> [Ann.Term Name]
        flattenApp'' as (Ann.App (Ann.Ann f _) (Ann.Ann a _)) =
          flattenApp'' (a:as) f
        flattenApp'' as (Ann.Loc _ a) =
          flattenApp'' as a
        flattenApp'' as f =
          f:as

    rawToMatch :: [Name] -> Bool -> Term Name -> Ques (Pattern Name)
    rawToMatch vars normalized (Local x)
      | elem x vars =
        return (Binding x)
      | otherwise =
        case Map.lookup x env of
          Just (DDataCons _, _) ->
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

    termToPattern :: [Name] -> Ann.Term Name -> Ques (LC.Pattern Name)
    termToPattern vars (Ann.Local x _)
      | elem x vars =
        return (LC.Binding x)
      | otherwise = do
        loc <- getLocation
        throwError ("Free variable at " ++ pprint loc ++ ".")
    termToPattern _ (Ann.Global x _) =
      return (LC.Constructor x [])
    termToPattern _ (Ann.App _ _) = do
      undefined
    termToPattern _ (Ann.Num x b) = do
      return (LC.NumPat x b)
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
    termToPattern vars (Ann.Loc loc t) =
      termToPattern vars t `locatedAt` loc

    checkEquation
      :: Env
      -> [(Name, Value, Ann.Term Ann.Name)]
      -> Value
      -> Ann.Term Ann.Name
      -> Term Name
      -> Value
      -> Ques ([(Name, LC.Type Name)], [LC.Pattern Name], LC.Term Name)
    checkEquation env vars lhsTy lhsAnn rhs ty' = do
      tell ["Checking vars of " ++ name]
      vars' <- mapM (\(name, _, annVarTy) -> (,) name <$> LC.cnvType annVarTy) vars
      tell ["Checking lhs of one of the equations of " ++ name ++ "; ctx: " ++ (show $ name : map (\(name', _, _) -> name') vars)]
      ps <- mapM (termToPattern (map (\(x, _, _) -> x) vars)) (tail (flattenApp' lhsAnn))
      tell ["Checking rhs of one of the equations of " ++ name ++ "; ctx: " ++ (show $ name : map (\(name', _, _) -> name') vars)]
      (rhsAnn, _) <- typeCheckAnn env vars rhs lhsTy
      tell ["Converting rhs to LC"]
      rhsLc <- LC.cnvBody rhsAnn
      tell ["Successful"]
      return (vars', ps, rhsLc)

    evalEquation :: Def Value Value -> [Pattern Name] -> Term Name -> ([Pattern Name], [(Name, Value)] -> Ques Value)
    evalEquation recur lhs' rhs =
      (lhs', \ctx -> eval (Map.insert name recur (Map.map fst env)) ctx rhs)
ttDeclToLcDecl env (TypeDecl name ty conss) = do
  (_, _) <- typeInfAnn env [] ty
  ty' <- eval (Map.map fst env) [] ty
  when
    (case ty' of VType 0 -> False; _ -> True)
    (throwError "Type definitions should be of ground types.")
  let env' = Map.insert name (DDataType ty', Ann.Type 1) env
  conss' <- mapM
      (\(consName, consTy) -> do
        tell ["Holi: " ++ show consTy]
        (_, consTyAnn) <- typeInfAnn env' [] consTy
        tell ["De camino: " ++ show consTyAnn]
        consTy' <- LC.cnvType consTyAnn
        tell ["Terminé"]
        return (consName, consTy', consTyAnn)
      )
      conss
  conss'' <- Map.fromList <$> mapM
    (\((consName, consTy), (_, _, consTyAnn)) -> do
      consTy' <- eval (Map.map fst env') [] consTy
      return (consName, (DDataCons consTy', consTyAnn))
    )
    (zip conss conss')
  return (LC.TypeDecl name (map (\(x, y, _) -> (x, y)) conss'), Map.union conss'' env')
