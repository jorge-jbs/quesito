{-# LANGUAGE ScopedTypeVariables #-}

module Quesito.Ann.Eval where
  
import Quesito
import Quesito.Ann
import Quesito.TT (BinOp(..), UnOp(..), Flags(..))
import qualified Quesito.Env as Env

import Data.List (find)
import Control.Monad (join)

type Env = Env.Env Def

type TContext =
  [(String, Value)]

type VContext =
  TContext

data Value
  = VLam String Type Term Closure
  | VType Int
  | VBytesType Int
  | VNum Int Int
  | VPi String Value Term Closure
  | VNormal Normal

data Normal
  = NFree String Type
  | NGlobal String Type
  | NDataType String Type
  | NDataCons String Type
  | NBinOp BinOp
  | NUnOp UnOp
  | NApp Normal Value

instance Eq Value where
  (==) = undefined

data Closure
  = Closure Env VContext

quote :: MonadQues m => Value -> m Term
quote (VLam x ty body _) =
  return (Lam x ty body)
quote (VType i) =
  return (Type i)
quote (VBytesType n) =
  return (BytesType n)
quote (VNum n b) =
  return (Num n b)
quote (VPi x v v' _) =
  Pi x <$> quote v <*> return v'
quote (VNormal n) =
  quoteNormal n
  where
    quoteNormal (NFree x ty) =
      return (Local x ty)
    quoteNormal (NGlobal x ty) =
      return (Global x ty)
    quoteNormal (NDataType x ty) =
      return (Global x ty)
    quoteNormal (NDataCons x ty) =
      return (Global x ty)
    quoteNormal (NBinOp op) =
      return (BinOp op)
    quoteNormal (NUnOp op) =
      return (UnOp op)
    quoteNormal (NApp m v) =
      App <$> quoteNormal m <*> quote v

eval :: MonadQues m => Env -> VContext -> Term -> m Value
eval _ ctx (Local x ty) =
  case lookup x ctx of
    Just v ->
      return v
    Nothing ->
     return (VNormal (NFree x ty))
eval env ctx (Global x ty) =
  case Env.lookup x env of
    Just (TypeDef n _ _) | x == n ->
      return (VNormal (NDataType x ty))
    Just (TypeDef {}) ->  -- x `elem` map fst conss
      return (VNormal (NDataCons x ty))
    Just (PatternMatchingDef _ [(_, [], f)] _ _) ->
      eval env [] f
    Just (PatternMatchingDef {}) ->
      return (VNormal (NGlobal x ty))
    Nothing -> do
      loc <- getLocation
      tell ("env: " ++ show (Env.keys env))
      tell ("ctx: " ++ show (map fst ctx))
      throwError ("Unknown global variable at " ++ pprint loc ++ ": " ++ x)
eval _ _ (Type lvl) =
  return (VType lvl)
eval _ _ (BytesType n) =
  return (VBytesType n)
eval _ _ (Num n b) =
  return (VNum n b)
eval _ _ (BinOp op) =
  return (VNormal (NBinOp op))
eval _ _ (UnOp op) =
  return (VNormal (NUnOp op))
eval env ctx (Pi x r s) = do
  r' <- eval env ctx r
  return (VPi x r' s (Closure env ctx))
eval env ctx (App r s) = do
  r' <- eval env ctx r
  s' <- eval env ctx s
  case r' of
    VLam x _ body (Closure env' ctx') ->
      eval env' ((x, s') : ctx') body
    VNormal n ->
      uncurry apply (flattenNormal (NApp n s'))
    _ ->
      undefined
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

    apply :: MonadQues m => Normal -> [Value] -> m Value
    apply (NBinOp Add) [VNum x b, VNum y _] = do
      return (VNum (x + y) b)
    apply (NBinOp Sub) [VNum x b, VNum y _] = do
      return (VNum (x - y) b)
    apply (NGlobal name _) args@(a:as) = do
      loc <- getLocation
      case Env.lookup name env of
        Just (PatternMatchingDef _ equations _ (Flags total)) ->
          if total then
            let
              matchedEq
                = join
                $ find (\x -> case x of Just _ -> True; _ -> False)
                $ map (\(_, p, body) -> do s <- matchEquation p args; return (s, body)) equations
            in
              case matchedEq of
                Just (s, t) ->
                  eval env s t
                Nothing ->
                  apply (NApp (NGlobal name undefined) a) as
          else
            apply (NApp (NGlobal name undefined) a) as
        --Just (DMatchFunction Nothing _ _) ->
          --apply (NApp (NGlobal name) a) as
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
    match (NumPat n) (VNum n' _) =
      if n < n' then
        Just []
      else
        Nothing
    match (NumPat _) _ =
      Nothing
    match (Constructor n) (VNormal (NDataCons n' _)) =
      if n == n' then
        Just []
      else
        Nothing
    match (Constructor _) _ =
      Nothing
    match (PatApp p p') (VNormal (NApp t t')) = do
      l <- match p (VNormal t)
      l' <- match p' t'
      return (l ++ l')
    match (PatApp _ _) _ =
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
eval env ctx (Lam x ty e) =
  return (VLam x ty e (Closure env ctx))
