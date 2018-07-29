module Quesito.Expr where

import Data.List (find)
import Data.Maybe (maybe)

import Control.Monad (unless)

data Name = Bound String | Binding String | Free String | Ignore
  deriving (Show, Eq)

-- | Inferable terms
data InfTerm
  = Var Name
  | Type Int
  | Pi Name CheckTerm CheckTerm
  | App InfTerm CheckTerm
  | Ann CheckTerm CheckTerm
  deriving (Show, Eq)

-- | Checkable terms
data CheckTerm
  = Inf InfTerm
  | Lam Name CheckTerm
  deriving (Show, Eq)

type Result a = Either String a

type Context = [(Name, CheckTerm)]
type Env = [(Name, CheckTerm)]

evalInf :: Env -> InfTerm -> CheckTerm
evalInf env (Var (Bound x)) =
  maybe
    (error ("Bound variable not found: " ++ x))
    id
    (snd <$> find ((\y' -> case y' of Binding y | x == y -> True; _ -> False) . fst) env)
evalInf _   (Var x) = Inf (Var x)
evalInf _   (Type lvl) = Inf (Type lvl)
evalInf _   (Pi x e e') = Inf (Pi x e e')
evalInf env (App e e') = case (evalInf env e, evalCheck env e') of
  (Lam x t, t') -> evalCheck ((x, t') : env) t
  (Inf (Pi x _ t), t') -> evalCheck ((x, t') : env) t
  _ -> error "Application to non-function."
evalInf env (Ann e _) = evalCheck env e

evalCheck :: Env -> CheckTerm -> CheckTerm
evalCheck env (Inf e) = evalInf env e
evalCheck _   (Lam x e) = Lam x e

typeInf :: Context -> InfTerm -> Result CheckTerm
typeInf ctx (Var (Bound x)) = case snd <$> find ((\y' -> case y' of Binding y | x == y -> True; _ -> False) . fst) ctx of
  Just t -> Right t
  Nothing -> fail "4"
typeInf _ (Var x) = Right (Inf (Var x))
typeInf _ (Type i) = Right (Inf (Type (i + 1)))
typeInf ctx (Pi x (Inf e) (Inf e')) = do
  t <- typeInf ctx e
  case t of
    Inf (Type i) -> do
      t' <- typeInf ((x, t) : ctx) e'
      case t' of
        Inf (Type j) ->
          return (Inf (Type (max i j)))
        _ -> fail "1"
    _ -> fail "2"
typeInf _ (Pi _ _ _) = fail ""
typeInf ctx (App e e') = do
  t <- typeInf ctx e
  case t of
    Inf t'@(Pi x r _) -> do
      typeCheck ((x, t) : ctx) e' r
      return (evalInf [] (App t' e'))
    _ -> fail "3"
typeInf ctx (Ann e ty) = do
  typeCheck ctx e ty
  return ty

typeCheck :: Context -> CheckTerm -> CheckTerm -> Result ()
typeCheck ctx (Lam x e) (Inf pi_@(Pi _ t _)) =
  typeCheck ((x, t) : ctx) e (evalInf [] (App pi_ (Inf (Var x))))
typeCheck _ (Lam _ _) _ = fail "6"
typeCheck ctx (Inf t) ty = do
  ty' <- typeInf ctx t
  unless (ty == ty') (fail "5")
