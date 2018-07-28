module Quesito.Expr where

import Data.List (find)
import Data.Maybe (maybe)

import Control.Monad (unless)

data Name = Bound String | Binding String | Free String | Ignore
  deriving (Show, Eq)

data Term
  = Var Name
  | Type Int
  | Pi Name Term Term
  | Lam Name Term Term
  | App Term Term
  deriving (Show, Eq)

type Result a = Either String a

type Context = [(Name, Term)]
type Env = [(Name, Term)]

eval :: Env -> Term -> Term
eval env (Var x) = maybe (Var x) id (snd <$> (find ((==) x . fst) env))
eval _   (Type lvl) = Type lvl
eval env (Pi x e e') = Pi x (eval env e) (eval env e')
eval env (Lam x e e') = Lam x (eval env e) (eval env e')
eval env (App e e') = case (eval env e, eval env e') of
  (Lam x _ t, t') -> eval ((x, t') : env) t
  (Pi x _ t, t') -> eval ((x, t') : env) t
  _ -> error "Application to non-function."

typeInf :: Context -> Term -> Result Term
typeInf ctx (Var (Bound x)) = case snd <$> find ((\y' -> case y' of Binding y | x == y -> True; _ -> False) . fst) ctx of
  Just t -> Right t
  Nothing -> fail "4"
typeInf _ (Var x) = Right (Var x)
typeInf _ (Type i) = Right (Type (i + 1))
typeInf ctx (Pi x e e') = do
  t <- typeInf ctx e
  case t of
    Type i -> do
      t' <- typeInf ((x, t) : ctx) e'
      case t' of
        Type j ->
          return (Type (max i j))
        _ -> fail "1"
    _ -> fail "2"
typeInf ctx (Lam x ty e) = do
  t <- typeInf ((x, ty) : ctx) e
  return (Pi Ignore ty t)
typeInf ctx (App e e') = do
  t <- typeInf ctx e
  t' <- typeInf ctx e'
  case t of
    Pi _ r _ | t' == r -> return (eval [] (App t e'))
    _ -> fail "3"

-- typeCheck :: Context -> Env -> CheckTerm -> CheckTerm -> Result ()
-- typeCheck ctx env (Lam x e) (Inf (Pi t t')) = do
--   typeCheck ((x, t) : ctx) env e t'
-- typeCheck ctx env (Inf e) t = do
--   t' <- typeInf ctx env e
--   unless (t == t') (fail "")
-- typeCheck _ _ _ _ = fail ""

-- typeCheck :: Term -> Context -> Term -> Result ()
-- typeCheck (Var x) d ty = do
--   let ty' = snd <$> find ((==) x . fst) d
--   if ty' == Just ty then
--     return ()
--   else
--     fail ""
-- typeCheck (Type i) _ (Type j) | i == j    = return ()
--                               | otherwise = fail ""
-- typeCheck (Pi r r') d (Pi t t') = do
--   let s = eval r d
--   let s' = eval r' d
--   if s == t && s' == t' then
--     return ()
--   else
--     fail ""
-- --typeCheck (Pi r r') d (Pi t t') = do
