{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT
  ( -- * Types
    Name
  , Term(..)
  , Value(..)
  , quote
    -- * Evaling
  , eval
    -- * Type checking
  , typeInf
  , typeCheck
    -- * Top-level
  , Def(..)
  , Decl(..)
  , checkDecl
  )
  where

import Prelude hiding (print)
import Control.Monad (unless, when, join)
import Data.Foldable (foldlM, foldl')
import Data.List (find)

import Quesito

class Printable a where
  print :: a -> String

type Name = String

instance Printable Name where
  print n =
    n

data Term v
  = Bound v
  | Free v
  | Type Int
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam Name (Term v)
  deriving Eq


instance Printable v => Show (Term v) where
  show (Bound v) =
    print v
  show (Free v) =
    print v
  show (Type i) =
    "(" ++ "Type " ++ show i ++ ")"
  show (Pi "" t t') =
    "(" ++ show t ++ " -> " ++ show t' ++ ")"
  show (Pi n t t') =
    "(" ++ "(" ++ n ++ " : "++ show t ++ ") -> " ++ show t' ++ ")"
  show (App t t') =
    "(" ++ show t ++ " " ++ show t' ++ ")"
  show (Ann t t') =
    "(" ++ show t ++ " " ++ show t' ++ ")"
  show (Lam n t) =
    "(" ++ "\\" ++ n ++ " -> " ++ show t ++ ")"

data Value
  = VLam Name (Value -> Ques Value)
  | VType Int
  | VPi Name Value (Value -> Ques Value)
  | VBound Name  -- used for quotation
  | VDataType Name
  | VDataCons Name
  | VFree Name
  | VApp Value Value

quote :: Value -> Ques (Term Name)
quote (VLam x f) =
  Lam x <$> (quote =<< f (VBound x))
quote (VType i) =
  return (Type i)
quote (VPi x v v') = do
  t <- quote v
  t' <- quote =<< v' (VBound x)
  return (Pi x t t')
quote (VBound x) =
  return (Bound x)
quote (VFree x) =
  return (Free x)
quote (VApp u v) = do
  u' <- quote u
  v' <- quote v
  return (App u' v')
quote (VDataType n) =
  return (Bound n)
quote (VDataCons n) =
  return (Bound n)

data DeBruijnVar = Index Int | DBFree Name
  deriving Eq

deBruijnize :: Term Name -> Term DeBruijnVar
deBruijnize =
  deBruijnize' []
  where
    deBruijnize' :: [Name] -> Term Name -> Term DeBruijnVar
    deBruijnize' vars (Bound v) =
      case takeWhile (\v' -> v /= v') vars of
        [] ->
          Bound (DBFree v)
        xs ->
          Bound (Index (length xs))
    deBruijnize' _ (Free v) =
      Free (DBFree v)
    deBruijnize' vars (Pi n t t') =
      Pi "" (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      Lam "" (deBruijnize' (n : vars) t)
    deBruijnize' _ (Type i) =
      Type i
    deBruijnize' vars (App t t') =
      App (deBruijnize' vars t) (deBruijnize' vars t')
    deBruijnize' vars (Ann t t') =
      Ann (deBruijnize' vars t) (deBruijnize' vars t')

data Def term ty
  = DExpr term ty
  | DDataType ty
  | DDataCons ty
  | DMatchFunction [([Pattern Name], [(Name, term)] -> Ques term)] ty

data Pattern name
  = Binding name
  | Inaccessible (Term name)
  | Constructor name
  | MatchApp (Pattern name) (Pattern name)
  deriving Show

type TContext =
  [(Name, Value)]

type VContext =
  TContext

type Env =
  [(Name, Def Value Value)]

eval :: Env -> VContext -> Term Name -> Ques Value
eval env ctx (Bound x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      return v
    Nothing ->
      case snd <$> find ((==) x . fst) env of
        Just (DExpr v _) ->
          return v
        Just (DDataType _) ->
          return (VDataType x)
        Just (DDataCons _) ->
          return (VDataCons x)
        Just (DMatchFunction [([], f)] _) ->
          f []
        Just (DMatchFunction _ _) ->
          return (VBound x)
        Nothing -> do
          loc <- getLocation
          tell ["env: " ++ show (map fst env)]
          tell ["ctx: " ++ show (map fst ctx)]
          throwError ("Found free variable at " ++ show loc ++ ": " ++ x)
eval _ _ (Free x) =
  return (VFree x)
eval _ _ (Type lvl) =
  return (VType lvl)
eval env ctx (Pi x e e') =
  VPi x <$> eval env ctx e <*> return (\t -> eval env ((x, t) : ctx) e')
eval env ctx (App e e') = do
  v <- eval env ctx e
  v' <- eval env ctx e'
  uncurry apply (flattenVApp (VApp v v'))
  where
    flattenVApp :: Value -> (Value, [Value])
    flattenVApp =
      flattenVApp' []
      where
        flattenVApp' :: [Value] -> Value -> (Value, [Value])
        flattenVApp' as (VApp f a) =
          flattenVApp' (a:as) f
        flattenVApp' as f =
          (f, as)

    apply :: Value -> [Value] -> Ques Value
    apply (VLam _ f) (a:as) = do
      x <- f a
      apply x as
    apply (VBound name) args@(a:as) = do
      loc <- getLocation
      case snd <$> find ((==) name . fst) env of
        Just (DMatchFunction equations _) ->
          let
            matchedEq
              = join
              $ find (\x -> case x of Just _ -> True; _ -> False)
              $ map (\(p, body) -> do s <- matchEquation p args; return (s, body)) equations
          in
            case matchedEq of
              Just (s, t) ->
                t s
              Nothing ->
                apply (VApp (VBound name) a) as
        Just _ ->
          throwError ("Variable should have been evaluated at " ++ show loc ++ ": " ++ name)
        Nothing ->
          throwError ("Free variable found at " ++ show loc ++ ": " ++ name)
    apply f (a:as) =
      apply (VApp f a) as
    apply f [] =
      return f

    match :: Pattern Name -> Value -> Maybe [(Name, Value)]
    match (Binding n) t =
      Just [(n, t)]
    match (Inaccessible _) _ =
      Just []
    match (Constructor n) (VDataCons n') =
      if n == n' then
        Just []
      else
        Nothing
    match (Constructor _) _ =
      Nothing
    match (MatchApp p p') (VApp t t') = do
      l <- match p t
      l' <- match p' t'
      return (l ++ l')
    match (MatchApp _ _) _ =
      Nothing

    matchEquation :: [Pattern Name] -> [Value] -> Maybe [(Name, Value)]
    matchEquation =
      matchEquation' []
      where
        matchEquation' :: [(Name, Value)] -> [Pattern Name] -> [Value] -> Maybe [(Name, Value)]
        matchEquation' l (p:ps) (v:vs) = do
          l' <- match p v
          matchEquation' (l ++ l') ps vs
        matchEquation' l [] [] =
          return l
        matchEquation' _ [] _ =
          Nothing
        matchEquation' _ _ [] =
          Nothing
eval env ctx (Ann e _) =
  eval env ctx e
eval env ctx (Lam x e) =
  return (VLam x (\v -> eval env ((x, v) : ctx) e))

typeInf :: Env -> TContext -> Term Name -> Ques Value
typeInf env ctx (Bound x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      return v
    Nothing ->
      case snd <$> find ((==) x . fst) env of
        Just (DExpr _ ty) ->
          return ty
        Just (DDataType ty) ->
          return ty
        Just (DDataCons ty) ->
          return ty
        Just (DMatchFunction _ ty) ->
          return ty
        Nothing -> do
          loc <- getLocation
          throwError ("Free variable at " ++ show loc ++ ": " ++ x)
typeInf env ctx (Free x) =
  typeInf env ctx (Bound x)
typeInf _ _ (Type i) =
  return (VType (i + 1))
typeInf env ctx (Pi x e f) = do
  t <- typeInf env ctx e
  case t of
    VType i -> do
      e' <- eval env [] e
      t' <-
        typeInf
          env
          ((x, e') : ctx)
          (subst x (Free x) f)
      case t' of
        VType j ->
          return (VType (max i j))
        _ -> do
          loc <- getLocation
          throwError ("1: " ++ show loc)
    _ -> do
      loc <- getLocation
      throwError ("2: " ++ show loc)
typeInf env ctx (App e f) = do
  s <- typeInf env ctx e
  case s of
    VPi _ t t' -> do
      typeCheck env ctx f t
      f' <- eval env [] f
      t' f'
    _ -> do
      loc <- getLocation
      qs <- quote s
      throwError ("Applying to non-function at " ++ show loc ++ ": " ++ show qs)
typeInf env ctx (Ann e ty) = do
  tyTy <- typeInf env ctx ty
  case tyTy of
    VType _ -> do
      ty' <- eval env [] ty
      typeCheck env ctx e ty'
      return ty'
    _ ->
      throwError ""
typeInf _ _ e@(Lam _ _) =
  throwError ("Can't infer type of lambda expression " ++ show e)

typeCheck :: Env -> TContext -> Term Name -> Value -> Ques ()
typeCheck env ctx (Lam x e) (VPi _ v w) = do
  w' <- w (VFree x)
  typeCheck env ((x, v) : ctx) (subst x (Free x) e) w'
typeCheck _ _ (Lam _ _) _ = do
  loc <- getLocation
  throwError ("6: " ++ show loc)
typeCheck env ctx t (VType j) = do
  t' <- typeInf env ctx t
  case t' of
    VType i  ->
      if i <= j then
        return ()
      else do
        loc <- getLocation
        throwError ("Incorrect type universe at " ++ show loc ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v -> do
      loc <- getLocation
      qv <- quote v
      throwError ("Expected type at " ++ show loc ++ " and got: " ++ show qv)
typeCheck env ctx t ty = do
  ty' <- typeInf env ctx t
  qty <- quote ty
  qty' <- quote ty'
  loc <- getLocation
  unless
    (deBruijnize qty == deBruijnize qty')
    (throwError ("Type mismatch at " ++ show loc ++ ". Expected " ++ show qty ++ " and got " ++ show qty'))

subst :: Name -> Term Name -> Term Name -> Term Name
subst name term (Bound name') =
  if name == name' then
    term
  else
    Bound name'
subst _ _ (Free name') =
  Free name'
subst _ _ (Type level) =
  Type level
subst name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (subst name term t) (subst name term t')
subst name term (App t t') =
  App (subst name term t) (subst name term t')
subst name term (Ann t t') =
  Ann (subst name term t) (subst name term t')
subst name term (Lam name' t) =
  if name == name' then
    Lam name' t
  else
    Lam name' (subst name term t)

freeVars :: [Name] -> Term Name -> Term Name
freeVars vars term =
  foldl' (\term' v -> subst v (Free v) term') term vars

data Decl
  = ExprDecl Name (Term Name) (Term Name)
  | MatchFunctionDecl Name [([(Name, Term Name)], Term Name, Term Name)] (Term Name)
  | TypeDecl
      Name
      (Term Name)  -- ^ Type
      [(Name, Term Name)]  -- ^ Constructors


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
            throwError ("Free variable at " ++ show loc ++ ".")
    rawToMatch vars normalized (Free x) =
      rawToMatch vars normalized (Bound x)
    rawToMatch vars _ (App l r) = do
      l' <- rawToMatch vars True l
      r' <- rawToMatch vars False r
      return (MatchApp l' r')
    rawToMatch _ _ (Type _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type universes (at " ++ show loc ++ ")")
    rawToMatch _ _ (Pi _ _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on function spaces (at " ++ show loc ++ ")")
    rawToMatch _ _ (Ann _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on type annotations (at " ++ show loc ++ ")")
    rawToMatch _ _ (Lam _ _) = do
      loc <- getLocation
      throwError ("Can't pattern match on lambda expressions (at " ++ show loc ++ ")")

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
    getReturnType x =
      x

    isConsOf :: Term Name -> Term Name -> Bool
    isConsOf (App e _) (Pi _ _ t) =
      isConsOf e t
    isConsOf (Bound name') (Type 0) | name == name' =
      True
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
