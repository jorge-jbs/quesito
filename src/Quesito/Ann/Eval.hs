{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Quesito.Ann.Eval where
  
import Quesito
import Quesito.Ann
import Quesito.TT (AttrLit(..), BinOp(..), UnOp(..), Flags(..))
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
  | VType Int Value
  | VBaseType Int
  | VUniquenessAttr
  | VBytesType Int
  | VNum Int Int
  | VAttrLit AttrLit
  | VAttr Value Value
  | VPi String Value Term Closure
  | VNormal Normal

data Normal
  = NFree String Type AttrLit
  | NHole Int Type
  | NGlobal String Type
  | NDataType String Type
  | NDataCons String Type
  | NBinOp BinOp
  | NUnOp UnOp
  | NApp Normal Value

isType :: Value -> Bool
isType (VType _ _) =
  True
isType _ =
  False

data Closure
  = Closure VContext

quote :: Value -> Term
quote (VLam x ty body _) =
  Lam x ty body
quote (VType i u) =
  Type i $ quote u
quote (VBaseType i) =
  BaseType i
quote VUniquenessAttr =
  UniquenessAttr
quote (VBytesType n) =
  BytesType n
quote (VNum n b) =
  Num n b
quote (VAttrLit u) =
  AttrLit u
quote (VAttr ty u) =
  Attr (quote ty) (quote u)
quote (VPi x v v' _) =
  Pi x (quote v) v'
quote (VNormal n) =
  quoteNormal n
  where
    quoteNormal (NFree x ty u) =
      Local x ty u
    quoteNormal (NHole i ty) =
      Hole i ty
    quoteNormal (NGlobal x ty) =
      Global x ty
    quoteNormal (NDataType x ty) =
      Global x ty
    quoteNormal (NDataCons x ty) =
      Global x ty
    quoteNormal (NBinOp op) =
      BinOp op
    quoteNormal (NUnOp op) =
      UnOp op
    quoteNormal (NApp m v) =
      App (quoteNormal m) (quote v)

eval
  :: (MonadLog m, MonadEnv Def m, MonadExcept m, MonadLocatable m)
  => VContext -> Term -> m Value
eval ctx (Local x ty u) =
  case lookup x ctx of
    Just v ->
      return v
    Nothing ->
      return (VNormal (NFree x ty u))
eval ctx (Hole x ty) =
  return (VNormal (NHole x ty))
eval ctx (Global x ty) = do
  env <- askEnv
  case Env.lookup x env of
    Just (TypeDef n _ _) | x == n ->
      return (VNormal (NDataType x ty))
    Just (TypeDef {}) ->  -- x `elem` map fst conss
      return (VNormal (NDataCons x ty))
    Just (PatternMatchingDef _ [(_, [], f)] _ _) ->
      eval [] f
    Just (PatternMatchingDef {}) ->
      return (VNormal (NGlobal x ty))
    Just (ExternDef {}) ->
      return (VNormal (NGlobal x ty))
    Nothing -> do
      loc <- askLoc
      env <- askEnv
      tell ("env: " ++ show (Env.keys env))
      tell ("ctx: " ++ show (map fst ctx))
      throwError ("Unknown global variable at " ++ pprint loc ++ ": " ++ x)
eval ctx (BaseType i) =
  return $ VBaseType i
eval ctx (Type i u) =
  VType i <$> eval ctx u
eval ctx (Attr ty u) =
  VAttr <$> eval ctx ty <*> eval ctx u
eval ctx UniquenessAttr =
  return $ VUniquenessAttr
eval ctx (AttrLit u) =
  return $ VAttrLit u
eval _ (BytesType n) =
  return (VBytesType n)
eval _ (Num n b) =
  return (VNum n b)
eval _ (BinOp op) =
  return (VNormal (NBinOp op))
eval _ (UnOp op) =
  return (VNormal (NUnOp op))
eval ctx (Pi x r s) = do
  r' <- eval ctx r
  return (VPi x r' s (Closure ctx))
eval ctx (App r s) = do
  r' <- eval ctx r
  s' <- eval ctx s
  case r' of
    VLam x _ body (Closure ctx') ->
      eval ((x, s') : ctx') body
    VNormal n ->
      let (x, y) = flattenNormal (NApp n s')
      in apply x (map simplify y)
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

    apply
      :: (MonadEnv Def m, MonadExcept m, MonadLocatable m, MonadLog m)
      => Normal
      -> [Value]
      -> m Value
    apply (NBinOp Add) [VNum x b, VNum y _] = do
      return (VNum (x + y) b)
    apply (NBinOp Sub) [VNum x b, VNum y _] = do
      return (VNum (x - y) b)
    apply (NGlobal name ty) args@(a:as) = do
      tell ("Applying " ++ name ++ " with " ++ show (map quote args))
      loc <- askLoc
      env <- askEnv
      case Env.lookup name env of
        Just (PatternMatchingDef _ equations _ (Flags total)) ->
          if total then
            let
              matchedEq
                = join
                $ find (\x -> case x of Just _ -> True; _ -> False)
                $ map
                    (\(_, p, body) -> do
                      x <- matchEquation p args
                      return (x, body)
                    )
                    equations
            in
              case matchedEq of
                Just (ctx', t) ->
                  eval ctx' t
                Nothing ->
                  apply (NApp (NGlobal name ty) a) as
          else
            apply (NApp (NGlobal name ty) a) as
        Just (ExternDef {}) ->
          apply (NApp (NGlobal name ty) a) as
        Just _ ->
          throwError ("Variable should have been evaluated at " ++ pprint loc ++ ": " ++ name)
        Nothing ->
          throwError ("Unknown global variable at " ++ pprint loc ++ ": " ++ name)
    apply f (a:as) =
      apply (NApp f a) as
    apply f [] =
      return (VNormal f)

    simplify :: Value -> Value
    simplify (VNormal (NApp (NApp (NBinOp Add) x@(VNum _ _)) y)) =
      simplify (VNormal (NApp (NApp (NBinOp Add) y) x))
    simplify (VNormal (NApp (NApp (NBinOp Add) x) (VNum 0 _))) =
      simplify x
    simplify v =
      v

    match :: Pattern -> Value -> Maybe [(String, Value)]
    match (Binding n _) t =
      Just [(n, t)]
    match (Inaccessible _) _ =
      Just []
    match (NumPat n _) (VNum n' _) =
      if n == n' then
        Just []
      else
        Nothing
    match (NumPat _ _) _ =
      Nothing
    match p'@(NumSucc p) (VNormal (NApp (NApp (NBinOp Add) x) y)) =
      case (simplify x, simplify y) of
        (_, VNum 0 _) ->
          match p' x
        (VNum 0 _, _) ->
          match p' y
        (_, VNum n b) ->
          match p $ simplify $ VNormal (NApp (NApp (NBinOp Add) x) (VNum (n-1) b))
        (VNum n b, _) ->
          match p $ simplify $ VNormal (NApp (NApp (NBinOp Add) (VNum (n-1) b)) y)
        _ ->
          Nothing
    match (NumSucc p) x | VNum n b <- simplify x =
      match p $ VNum (n-1) b
    match (NumSucc _) _ =
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
eval ctx (Lam x ty e) = do
  return $ VLam x ty e $ Closure ctx
