{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT
  ( -- * Types
    Name
  , Pos(..)
  , Term(..)
  , TermKind(..)
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
import Data.Bifunctor (first)
import Data.Foldable (foldlM, foldl')
import Data.List (find)

import Quesito

class Printable a where
  print :: a -> String

type Name = String

instance Printable Name where
  print n =
    n

data TermKind v
  = Bound v
  | Free v
  | Type Int
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam Name (Term v)
  deriving Eq

data Pos
  = Pos
      Int  -- ^ line
      Int  -- ^ column
  | None
  deriving Eq

instance Show Pos where
  show (Pos y x) =
    "line " ++ show y ++ " and column " ++ show x
  show None =
    "MISSING"

data Term v = Term Pos (TermKind v)

instance Printable v => Show (TermKind v) where
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

instance Printable v => Show (Term v) where
  show (Term _ k) =
    show k

instance Eq v => Eq (Term v) where
  Term _ t == Term _ t' =
    t == t'

data Value
  = VLam Name (Value -> Value)
  | VType Int
  | VPi Name Value (Value -> Value)
  | VBound Name  -- used for quotation
  | VDataType Name
  | VDataCons Name
  | VFree Name
  | VApp Value Value

quote :: Value -> Term Name
quote (VLam x f) =
  Term None (Lam x (quote (f (VBound x))))
quote (VType i) =
  Term None (Type i)
quote (VPi x v v') =
  Term None (Pi x t t')
  where
    t = quote v
    t' = quote (v' (VBound x))
quote (VBound x) =
  Term None (Bound x)
quote (VFree x) =
  Term None (Free x)
quote (VApp u v) =
  Term None (App u' v')
  where
    u' = quote u
    v' = quote v
quote (VDataType n) =
  Term None (Bound n)
quote (VDataCons n) =
  Term None (Bound n)

data DeBruijnVar = Index Int | DBFree Name
  deriving Eq

deBruijnize :: Term Name -> Term DeBruijnVar
deBruijnize =
  deBruijnize' []
  where
    deBruijnize' :: [Name] -> Term Name -> Term DeBruijnVar
    deBruijnize' vars (Term pos k) =
      case k of
        Bound v ->
          case takeWhile (\v' -> v /= v') vars of
            [] ->
              Term pos (Bound (DBFree v))
            xs ->
              Term pos (Bound (Index (length xs)))
        Free v ->
          Term pos (Free (DBFree v))
        Pi n t t' ->
          Term pos (Pi "" (deBruijnize' vars t) (deBruijnize' (n : vars) t'))
        Lam n t ->
          Term pos (Lam "" (deBruijnize' (n : vars) t))
        Type i ->
          Term pos (Type i)
        App t t' ->
          Term pos (App (deBruijnize' vars t) (deBruijnize' vars t'))
        Ann t t' ->
          Term pos (Ann (deBruijnize' vars t) (deBruijnize' vars t'))

data Def term ty
  = DExpr term ty
  | DDataType ty
  | DDataCons ty
  | DMatchFunction [([Pattern Name], [(Name, term)] -> term)] ty

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

eval :: Env -> VContext -> Term Name -> Value
eval env ctx (Term pos k) =
  case k of
    Bound x ->
      case snd <$> find ((==) x . fst) ctx of
        Just v ->
          v
        Nothing ->
          case snd <$> find ((==) x . fst) env of
            Just (DExpr v _) ->
              v
            Just (DDataType _) ->
              VDataType x
            Just (DDataCons _) ->
              VDataCons x
            Just (DMatchFunction [([], f)] _) ->
              f []
            Just (DMatchFunction _ _) ->
              VBound x
            Nothing ->
              error ("Found free variable at " ++ show pos ++ ": " ++ x)
    Free x ->
      VFree x
    Type lvl ->
      VType lvl
    Pi x e e' ->
      VPi x (eval env ctx e) (\t -> eval env ((x, t) : ctx) e')
    App e e' ->
      uncurry apply (flattenVApp (VApp (eval env ctx e) (eval env ctx e')))
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

        apply :: Value -> [Value] -> Value
        apply (VLam _ f) (a:as) =
          apply (f a) as
        apply (VBound name) args@(a:as) =
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
              error ("Variable should have been evaluated at " ++ show pos ++ ": " ++ name)
            Nothing ->
              error ("Free variable found at " ++ show pos ++ ": " ++ name)
        apply f (a:as) =
          apply (VApp f a) as
        apply f [] =
          f

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
    Ann e _ ->
      eval env ctx e
    Lam x e ->
      VLam x (\v -> eval env ((x, v) : ctx) e)

typeInf :: Env -> TContext -> Term Name -> Ques Value
typeInf env ctx (Term pos k) =
  case k of
    Bound x ->
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
            Nothing ->
              throwError ("Free variable at " ++ show pos ++ ": " ++ x)
    Free x ->
      typeInf env ctx (Term pos (Bound x))
    Type i ->
      return (VType (i + 1))
    Pi x e e' -> do
      t <- typeInf env ctx e
      case t of
        VType i -> do
          t' <-
            typeInf
              env
              ((x, eval env [] e) : ctx)
              (subst x (Free x) e')
          case t' of
            VType j ->
              return (VType (max i j))
            _ ->
              throwError ("1: " ++ show pos)
        _ ->
          throwError ("2: " ++ show pos)
    App e e' -> do
      s <- typeInf env ctx e
      case s of
        VPi _ t t' -> do
          typeCheck env ctx e' t
          return (t' (eval env [] e'))
        _ ->
          throwError ("Applying to non-function at " ++ show pos ++ ": " ++ show (quote s))
    Ann e ty -> do
      tyTy <- typeInf env ctx ty
      case tyTy of
        VType _ -> do
          let ty' = eval env [] ty
          typeCheck env ctx e ty'
          return ty'
        _ ->
          throwError ""
    e@(Lam _ _) ->
      throwError ("Can't infer type of lambda expression " ++ show e)

typeCheck :: Env -> TContext -> Term Name -> Value -> Ques ()
typeCheck env ctx (Term _ (Lam x e)) (VPi _ t t') =
  typeCheck env ((x, t) : ctx) (subst x (Free x) e) (t' (VFree x))
typeCheck _ _ (Term pos (Lam _ _)) _ =
  throwError ("6: " ++ show pos)
typeCheck env ctx t@(Term pos _) (VType j) = do
  t' <- typeInf env ctx t
  case t' of
    VType i  ->
      if i <= j then
        return ()
      else
        throwError ("Incorrect type universe at " ++ show pos ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v ->
      throwError ("Expected type at " ++ show pos ++ " and got: " ++ show (quote v))
typeCheck env ctx t@(Term pos _) ty = do
  ty' <- typeInf env ctx t
  unless
    (deBruijnize (quote ty) == deBruijnize (quote ty'))
    (throwError ("Type mismatch at " ++ show pos ++ ". Expected " ++ show (quote ty) ++ " and got " ++ show (quote ty')))

subst :: Name -> TermKind Name -> Term Name -> Term Name
subst name term (Term pos k) =
  case k of
    Bound name' ->
      if name == name' then
        Term pos term
      else
        Term pos (Bound name')
    Free name' ->
      Term pos (Free name')
    Type level ->
      Term pos (Type level)
    Pi name' t t' ->
      if name == name' then
        Term pos (Pi name' t t')
      else
        Term pos (Pi name' (subst name term t) (subst name term t'))
    App t t' ->
      Term pos (App (subst name term t) (subst name term t'))
    Ann t t' ->
      Term pos (Ann (subst name term t) (subst name term t'))
    Lam name' t ->
      if name == name' then
        Term pos (Lam name' t)
      else
        Term pos (Lam name' (subst name term t))

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
  tyTy <-
    typeInf env [] ty `catchError`
      \err -> throwError ("Type error while checking " ++ name ++ ": " ++ err)

  case tyTy of
    VType _ -> do
      let ty' = eval env [] ty
      typeCheck ((name, DExpr undefined ty') : env) [] (subst name (Free name) expr) ty'
      let expr' = eval ((name, DExpr expr' ty') : env) [] expr
      return [(name, DExpr expr' ty')]
    _ ->
      throwError (name ++ "'s type is not of kind Type.")

checkDecl env (MatchFunctionDecl name equations ty) = do
  typeCheck env [] ty (VType 1000)
  let ty' = eval env [] ty
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
          return ((name', eval env [] freedTy') : vars')
        )
        []
        vars

    flattenApp :: Term Name -> [Term Name]
    flattenApp =
      flattenApp' []
      where
        flattenApp' :: [Term Name] -> Term Name -> [Term Name]
        flattenApp' as (Term _ (App f a)) =
          flattenApp' (a:as) f
        flattenApp' as f =
          f:as

    rawToMatch :: [Name] -> Bool -> Term Name -> Ques (Pattern Name)
    rawToMatch vars normalized (Term pos (Bound x))
      | elem x vars =
        return (Binding x)
      | otherwise =
        case find ((==) x . fst) env of
          Just (_, DDataCons _) ->
            return (Constructor x)
          Just _ | not normalized ->
            return (Inaccessible (Term pos (Bound x)))
          _ ->
            throwError ("Free variable at " ++ show pos ++ ".")
    rawToMatch vars normalized (Term pos (Free x)) =
      rawToMatch vars normalized (Term pos (Bound x))
    rawToMatch vars _ (Term _ (App l r)) = do
      l' <- rawToMatch vars True l
      r' <- rawToMatch vars False r
      return (MatchApp l' r')
    rawToMatch _ _ (Term pos (Type _)) =
      throwError ("Can't pattern match on type universes (at " ++ show pos ++ ")")
    rawToMatch _ _ (Term pos (Pi _ _ _)) =
      throwError ("Can't pattern match on function spaces (at " ++ show pos ++ ")")
    rawToMatch _ _ (Term pos (Ann _ _)) =
      throwError ("Can't pattern match on type annotations (at " ++ show pos ++ ")")
    rawToMatch _ _ (Term pos (Lam _ _)) =
      throwError ("Can't pattern match on lambda expressions (at " ++ show pos ++ ")")

    checkEquation :: [(Name, Value)] -> Term Name -> Term Name -> Value -> Ques ()
    checkEquation vars lhs rhs ty' = do
      let freedLhs = freeVars (map fst vars) lhs
      let freedRhs = freeVars (map fst vars) rhs
      lhsTy <- typeInf env ((name, ty') : vars) freedLhs
      typeCheck env ((name, ty') : vars) freedRhs lhsTy

    evalEquation :: Def Value Value -> [Pattern Name] -> Term Name -> ([Pattern Name], [(Name, Value)] -> Value)
    evalEquation recur lhs' rhs =
      (lhs', \ctx -> eval ((name, recur):env) ctx rhs)

checkDecl env (TypeDecl name ty conss) = do
  tyTy <- typeInf env [] ty
  case tyTy of
    VType _ ->
      case getReturnType ty of
        Term _ (Type 0) -> do
          let typeDef = (name, DDataType (eval env [] ty))
          conss' <- mapM (uncurry (checkCons typeDef)) conss
          return (typeDef : conss')
        _ ->
          throwError (name ++ " is not a ground type.")
    _ ->
      throwError (name ++ "'s type is not of kind Type.")
  where
    getReturnType :: Term Name -> Term Name
    getReturnType (Term _ (Pi _ _ x)) =
      getReturnType x
    getReturnType x =
      x

    isConsOf :: Term Name -> Term Name -> Bool
    isConsOf (Term _ (App e _)) (Term _ (Pi _ _ t)) =
      isConsOf e t
    isConsOf (Term _ (Bound name')) (Term _ (Type 0)) | name == name' =
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
      return (name', DDataCons (eval env' [] consTy))
