module UntypedLambdaCalculus where

import Parse

data Term
  = Var Char
  | Lambda Char Term
  | App Term Term
  deriving (Show)

replace :: Term -> Char -> Term -> Term
replace t@(Var x) v t' = if x == v then t' else t
replace t@(Lambda x s) v t' =
  if x == v then
    t
  else
    Lambda x (replace s v t')
replace (App t t') v t'' = App (replace t v t'') (replace t' v t'')

beta :: Term -> Term
beta (App (Lambda v t) t') = replace t v t'
beta (App t t') = App (beta t) (beta t')
beta t = t

toLambda :: AST -> Maybe Term
toLambda (Symbol str) =
  if length str == 1 then
    Just $ Var $ head str
  else
    Nothing
toLambda (Num _) = Nothing
toLambda (List es) =
  if length es == 2 then do
    e  <- toLambda $ head es
    e' <- toLambda $ head $ tail es
    return $ App e e'
  else if length es == 3 && es !! 0 == Symbol "lambda" then do
    v <- case toLambda $ head $ tail es of
      Just (Var v) -> Just v
      _ -> Nothing
    t <- toLambda $ head $ tail $ tail es
    return $ Lambda v t
  else
    Nothing
