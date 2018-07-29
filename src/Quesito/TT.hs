module Quesito.TT where

import Data.List (find)
import Data.Maybe (maybe)

import Control.Monad (unless)

type Name = String

data Var = Bound Name | Free Name
  deriving (Show, Eq)

-- | Inferable terms
data InfTerm
  = Var Var
  | Type Int
  | Pi Name InfTerm InfTerm
  | App InfTerm CheckTerm
  | Ann CheckTerm InfTerm
  deriving (Show, Eq)

-- | Checkable terms
data CheckTerm
  = Inf InfTerm
  | Lam Name CheckTerm
  deriving (Show, Eq)

data Value
  = VLam Name (Value -> Value)
  | VType Int
  | VPi Name Value (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NBound Name  -- Only used for quotation
  | NApp Neutral Value

quote :: Value -> CheckTerm
quote (VLam x f) = Lam x (quote (f (VNeutral (NBound x))))
quote (VType i) = Inf (Type i)
quote (VPi x v v') = Inf (Pi x t t')
  where
    Inf t = quote v
    Inf t' = quote (v' (VNeutral (NFree x)))
quote (VNeutral (NFree x)) = Inf (Var (Free x))
quote (VNeutral (NBound x)) = Inf (Var (Bound x))
quote (VNeutral (NApp n v)) = Inf (App n' v')
  where
    Inf n' = quote (VNeutral n)
    v' = quote v

type Result a = Either String a

type Context = [(Name, Value)]
type Env = [(Name, Value)]

evalInf :: Env -> InfTerm -> Value
evalInf env (Var (Bound x)) =
  maybe
    (error ("Bound variable not found: " ++ x))
    id
    (snd <$> find ((\y' -> case y' of y | x == y -> True; _ -> False) . fst) env)
evalInf _   (Var (Free x)) = VNeutral (NFree x)
evalInf _   (Type lvl) = VType lvl
evalInf env (Pi x e e') = VPi x (evalInf env e) (\t -> evalInf ((x, t) : env) e')
evalInf env (App e e') = case (evalInf env e, evalCheck env e') of
  (VLam _ t, t') -> t t'
  (VNeutral n, v) -> VNeutral (NApp n v)
  _ -> error "Application to non-function."
evalInf env (Ann e _) = evalCheck env e

evalCheck :: Env -> CheckTerm -> Value
evalCheck env (Inf e) = evalInf env e
evalCheck env (Lam x e) = VLam x (\v -> evalCheck ((x, v) : env) e)

typeInf :: Context -> InfTerm -> Result Value
typeInf ctx (Var (Bound x)) = case snd <$> find ((\y' -> case y' of y | x == y -> True; _ -> False) . fst) ctx of
  Just t -> Right t
  Nothing -> Left "4"
typeInf ctx (Var (Free x)) = case snd <$> find ((\y' -> case y' of y | x == y -> True; _ -> False) . fst) ctx of
  Just t -> Right t
  Nothing -> Left x
typeInf _ (Type i) = Right (VType (i + 1))
typeInf ctx (Pi x e e') = do
  t <- typeInf ctx e
  case t of
    VType i -> do
      t' <- typeInf ((x, t) : ctx) e'
      case t' of
        VType j ->
          return (VType (max i j))
        _ -> Left "1"
    _ -> Left "2"
typeInf ctx (App e e') = do
  s <- typeInf ctx e
  case s of
    VPi _ t t' -> do
      typeCheck ctx e' t
      return (t' (evalCheck [] e'))
    _ -> Left "3"
typeInf ctx (Ann e ty) = do
  tyTy <- typeInf ctx ty
  case tyTy of
    VType _ -> do
      let ty' = evalInf [] ty
      typeCheck ctx e ty'
      return ty'
    _ -> Left ""

typeCheck :: Context -> CheckTerm -> Value -> Result ()
typeCheck ctx (Lam x e) (VPi _ t t') =
  typeCheck ((x, t) : ctx) e (t' (VNeutral (NFree x)))
typeCheck _ (Lam _ _) _ = Left "6"
typeCheck ctx (Inf t) ty = do
  ty' <- typeInf ctx t
  unless (quote ty == quote ty') (Left "5")
