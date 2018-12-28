module Quesito.TT.Eval where

import Quesito
import Quesito.TT

import Data.List (find)
import Control.Monad (join)

data Def term ty
  = DExpr term ty
  | DDataType ty
  | DDataCons ty
  | DMatchFunction [([Pattern Name], [(Name, term)] -> Ques term)] ty

data Pattern name
  = Binding name
  | Inaccessible (Term name)
  | NumPat Int
  | Constructor name
  | MatchApp (Pattern name) (Pattern name)
  deriving Show

type TContext =
  [(Name, Value)]

type VContext =
  TContext

type Env =
  [(Name, Def Value Value)]

data Value
  = VLam Name (Value -> Ques Value)
  | VType Int
  | VBytesType Int
  | VNum Int
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
quote (VBytesType n) =
  return (BytesType n)
quote (VNum n) =
  return (Num n)
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
  return (Free n)
quote (VDataCons n) =
  return (Free n)

eval :: Env -> VContext -> Term Name -> Ques Value
eval env ctx (Bound x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      return v
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (map fst env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Found free variable at " ++ pprint loc ++ ": " ++ x)
eval env ctx (Free x) =
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
      return (VFree x)
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (map fst env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Found free variable at " ++ pprint loc ++ ": " ++ x)
eval _ _ (Type lvl) =
  return (VType lvl)
eval _ _ (BytesType n) =
  return (VBytesType n)
eval _ _ (Num n) =
  return (VNum n)
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
          throwError ("Variable should have been evaluated at " ++ pprint loc ++ ": " ++ name)
        Nothing ->
          throwError ("Free variable found at " ++ pprint loc ++ ": " ++ name)
    apply f (a:as) =
      apply (VApp f a) as
    apply f [] =
      return f

    match :: Pattern Name -> Value -> Maybe [(Name, Value)]
    match (Binding n) t =
      Just [(n, t)]
    match (Inaccessible _) _ =
      Just []
    match (NumPat n) (VNum n') =
      if n < n' then
        Just []
      else
        Nothing
    match (NumPat _) _ =
      Nothing
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
eval env ctx (Loc loc t) =
  eval env ctx t `locatedAt` loc
