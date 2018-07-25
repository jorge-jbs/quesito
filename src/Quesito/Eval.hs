module Quesito.Eval (eval) where

import Quesito.Constant
import Quesito.Expr

replace :: QuesExpr -> Var -> QuesExpr -> QuesExpr
replace t@(Var x) v t' = if x == v then t' else t
replace t@(Lambda x ty s) v t' =
  if x == v then
    t
  else
    Lambda x ty (replace s v t')
replace (App t t') v t'' = App (replace t v t'') (replace t' v t'')
replace r@(Let (u, s) t) v p =
  if u == v then
    r
  else
    Let (u, (replace s v p)) (replace t v p)
replace t _ _ = t

beta :: QuesExpr -> QuesExpr
beta (App (Lambda v _ t) t') = replace t v t'
beta (App t t') = App (beta t) (beta t')
beta t = t

eval :: QuesExpr -> QuesExpr
eval (App t t') = case t of
  Constant Plus2 ->
    let Constant (Quesito.Constant.Num x) = t'
    in Constant (Plus1 x)
  Constant (Plus1 x) ->
    let Constant (Quesito.Constant.Num y) = t'
    in Constant (Quesito.Constant.Num (x+y))
  _ -> eval (beta (App (eval t) (eval t')))
eval (Let (v, t) t') = eval (replace t' v t)
eval t = t
