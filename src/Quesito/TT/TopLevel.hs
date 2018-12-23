module Quesito.TT.TopLevel where

import Quesito
import Quesito.TT
import Quesito.TT.Eval hiding (Env)
import Quesito.TT.TypeCheck hiding (Env)
import Quesito.TT.TypeAnn
import qualified Quesito.Ann as Ann
import qualified Quesito.LC as LC
import qualified Quesito.LC.TopLevel as LC

import Data.Foldable (foldlM)
import Data.List (find)
import Control.Monad (when)

data Decl
  = ExprDecl Name (Term Name) (Term Name)
  -- | MatchFunctionDecl Name [([(Name, Term Name)], Term Name, Term Name)] (Term Name)
  | TypeDecl
      Name
      (Term Name)  -- ^ Type
      [(Name, Term Name)]  -- ^ Constructors
  deriving Show

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
          Just (_, DDataCons _) ->
            return (Constructor x)
          Just _ | not normalized ->
            return (Inaccessible (Bound x))
          _ -> do
            loc <- getLocation
            throwError ("Free variable at " ++ pprint loc ++ ".")
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

checkDecl env (TypeDecl name ty conss) = do
  tyTy <- typeInf env [] ty
  case tyTy of
    VType _ ->
      case getReturnType ty of
        Type 0 -> do
          ty' <- eval env [] ty
          let typeDef = (name, DDataType ty')
          conss' <- mapM (uncurry (checkCons typeDef)) conss
          return (typeDef : conss')
        _ ->
          throwError (name ++ " is not a ground type.")
    _ ->
      throwError (name ++ "'s type is not of kind Type.")
  where
    getReturnType :: Term Name -> Term Name
    getReturnType (Pi _ _ x) =
      getReturnType x
    getReturnType (Loc _ x) =
      getReturnType x
    getReturnType x =
      x

    isConsOf :: Term Name -> Term Name -> Bool
    isConsOf (App e _) (Pi _ _ t) =
      isConsOf e t
    isConsOf (Bound name') (Type 0) | name == name' =
      True
    isConsOf (Loc _ e) t =
      isConsOf e t
    isConsOf e (Loc _ t) =
      isConsOf e t
    isConsOf _ _ =
      False

    checkCons :: (Name, Def Value Value) -> Name -> Term Name -> Ques (Name, Def Value Value)
    checkCons typeDef name' consTy = do
      let env' = typeDef : env
      tyTy <-
          typeInf env' [] consTy `catchError`
            \err -> throwError ("Type error while checking " ++ name' ++ ": " ++ err)
      when
        (case tyTy of VType _ -> False; _ -> True)
        (throwError (name' ++ "'s type is not of kind Type."))
      when
        (not (isConsOf (getReturnType consTy) ty))
        (throwError (name' ++ " is not a constructor for " ++ name ++ "."))
      consTy' <- eval env' [] consTy
      return (name', DDataCons consTy')

ttDeclToLcDecl :: Env -> Decl -> Ques (LC.Decl, Env)
ttDeclToLcDecl env (ExprDecl name expr ty) = do
  (_, annTy) <- typeInfAnn env [] ty
  expr' <- eval (discardThird env) [] expr
  ty' <- eval (discardThird env) [] ty
  (annExpr, _) <- typeCheckAnn env [] expr ty'
  (args, body, retTy) <- flatten annExpr annTy []
  return (LC.ExprDecl name args body retTy, (name, DExpr expr' ty', annTy) : env)
  where
    flatten
      :: Ann.Term Ann.Name
      -> Ann.Term Ann.Name
      -> [(Ann.Name, Ann.Term Ann.Name)]
      -> Ques ([(LC.Name, LC.Type LC.Name)], LC.Term LC.Name, LC.Type LC.Name)
    flatten (Ann.Loc loc t) ty' ctx =
      flatten t ty' ctx `locatedAt` loc
    flatten (Ann.Lam argName ty1 (Ann.Ann t ty2)) _ ctx = do
      ty1' <- LC.cnvType ty1
      (args, body, retTy) <- flatten t ty2 ((argName, ty1) : ctx)
      return ((argName, ty1') : args, body, retTy)
    flatten body retTy _ = do
      body' <- LC.cnvBody body
      retTy' <- LC.cnvType retTy
      return ([], body', retTy')
ttDeclToLcDecl env (TypeDecl name ty conss) = do
  (_, _) <- typeInfAnn env [] ty
  ty' <- eval (discardThird env) [] ty
  when
    (case ty' of VType 0 -> False; _ -> True)
    (throwError "Type definitions should be of ground types.")
  let env' = (name, DDataType ty', Ann.Type 1) : env
  conss' <- mapM
      (\(consName, consTy) -> do
        tell ["Holi: " ++ show consTy]
        (_, consTyAnn) <- typeInfAnn env' [] consTy
        tell ["De camino: " ++ show consTyAnn]
        consTy' <- LC.cnvType consTyAnn
        tell ["Terminé"]
        return (consName, consTy')
      )
      conss
  return (LC.TypeDecl name conss', env)
