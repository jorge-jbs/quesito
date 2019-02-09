module Quesito.TT.Eval where

import Quesito
import Quesito.TT

import Data.List (find)
import qualified Data.Map as Map
import Control.Monad (join)

data Flags =
  Flags
    { total :: Bool
    }
  deriving Show

data Def term ty
  = DDataType ty
  | DDataCons ty
  | DMatchFunction (Maybe [([Pattern], [(String, term)] -> Ques term)]) ty Flags

data Pattern
  = Binding String
  | Inaccessible Term
  | NumPat Int
  | Constructor String
  | MatchApp Pattern Pattern
  deriving Show

type TContext =
  [(String, Value)]

type VContext =
  TContext

type Env =
  Map.Map String (Def Value Value)

data Value
  = VLam String (Value -> Ques Value)
  | VType Int
  | VBytesType Int
  | VNum Int
  | VPi String Value (Value -> Ques Value)
  | VNormal Normal

data Normal
  = NFree String
  | NGlobal String
  | NDataType String
  | NDataCons String
  | NBinOp BinOp
  | NUnOp UnOp
  | NApp Normal Value

quote :: Value -> Ques (Term)
quote (VLam x f) =
  Lam x <$> (quote =<< f (VNormal (NFree x)))
quote (VType i) =
  return (Type i)
quote (VBytesType n) =
  return (BytesType n)
quote (VNum n) =
  return (Num n)
quote (VPi x v v') = do
  t <- quote v
  t' <- quote =<< v' (VNormal (NFree x))
  return (Pi x t t')
quote (VNormal n) =
  quoteNormal n
  where
    quoteNormal (NFree n) =
      return (Local n)
    quoteNormal (NGlobal n) =
      return (Global n)
    quoteNormal (NDataType n) =
      return (Global n)
    quoteNormal (NDataCons n) =
      return (Global n)
    quoteNormal (NBinOp op) =
      return (BinOp op)
    quoteNormal (NUnOp op) =
      return (UnOp op)
    quoteNormal (NApp n v) =
      App <$> quoteNormal n <*> quote v

eval :: Env -> VContext -> Term -> Ques Value
eval _ ctx (Local x) =
  case lookup x ctx of
    Just v ->
      return v
    Nothing ->
     return (VNormal (NFree x))
eval env ctx (Global x) =
  case Map.lookup x env of
    Just (DDataType _) ->
      return (VNormal (NDataType x))
    Just (DDataCons _) ->
      return (VNormal (NDataCons x))
    Just (DMatchFunction (Just [([], f)]) _ _) ->
      f []
    Just (DMatchFunction _ _ _) ->
      return (VNormal (NGlobal x))
    Nothing -> do
      loc <- getLocation
      tell ["env: " ++ show (Map.keys env)]
      tell ["ctx: " ++ show (map fst ctx)]
      throwError ("Unknown global variable at " ++ pprint loc ++ ": " ++ x)
eval _ _ (Type lvl) =
  return (VType lvl)
eval _ _ (BytesType n) =
  return (VBytesType n)
eval _ _ (Num n) =
  return (VNum n)
eval _ _ (BinOp op) =
  return (VNormal (NBinOp op))
eval _ _ (UnOp op) =
  return (VNormal (NUnOp op))
eval env ctx (Pi x e e') =
  VPi x <$> eval env ctx e <*> return (\t -> eval env ((x, t) : ctx) e')
eval env ctx (App e e') = do
  v <- eval env ctx e
  v' <- eval env ctx e'
  case v of
    VLam _ f ->
      f v'
    VNormal n ->
      uncurry apply (flattenNormal (NApp n v'))
  where
    flattenNormal :: Normal -> (Normal, [Value])
    flattenNormal =
      flattenNormal' []
      where
        flattenNormal' :: [Value] -> Normal -> (Normal, [Value])
        flattenNormal' as (NApp f a) =
          flattenNormal' (a:as) f
        flattenNormal' as f =
          (f, as)

    apply :: Normal -> [Value] -> Ques Value
    apply (NBinOp Add) [VNum x, VNum y] = do
      return (VNum (x + y))
    apply (NBinOp Sub) [VNum x, VNum y] = do
      return (VNum (x - y))
    apply (NGlobal name) args@(a:as) = do
      loc <- getLocation
      case Map.lookup name env of
        Just (DMatchFunction (Just equations) _ (Flags total)) ->
          if total then
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
                  apply (NApp (NGlobal name) a) as
          else do
            apply (NApp (NGlobal name) a) as
        Just (DMatchFunction Nothing _ (Flags total)) ->
          apply (NApp (NGlobal name) a) as
        Just _ ->
          throwError ("Variable should have been evaluated at " ++ pprint loc ++ ": " ++ name)
        Nothing ->
          throwError ("Unknown global variable at " ++ pprint loc ++ ": " ++ name)
    apply f (a:as) =
      apply (NApp f a) as
    apply f [] =
      return (VNormal f)

    match :: Pattern -> Value -> Maybe [(String, Value)]
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
    match (Constructor n) (VNormal (NDataCons n')) =
      if n == n' then
        Just []
      else
        Nothing
    match (Constructor _) _ =
      Nothing
    match (MatchApp p p') (VNormal (NApp t t')) = do
      l <- match p (VNormal t)
      l' <- match p' t'
      return (l ++ l')
    match (MatchApp _ _) _ =
      Nothing

    matchEquation :: [Pattern] -> [Value] -> Maybe [(String, Value)]
    matchEquation =
      matchEquation' []
      where
        matchEquation' :: [(String, Value)] -> [Pattern] -> [Value] -> Maybe [(String, Value)]
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
