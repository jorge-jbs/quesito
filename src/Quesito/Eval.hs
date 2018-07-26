module Quesito.Eval (eval) where

import Quesito.Constant as C
import Quesito.Expr

replace :: QuesExpr -> Var -> QuesExpr -> QuesExpr
replace (Var u) v t = if u == v then t else Var u
replace (Lambda u ty r) v s =
  Lambda u ty
    (
      if u == v then
        r
      else
        replace r v s
    )
replace (App t t') v t'' = App (replace t v t'') (replace t' v t'')
replace r@(Let (u, ty, s) t) v p =
  if u == v then
    r
  else
    Let (u, ty, (replace s v p)) (replace t v p)
replace (Pair r s) v t = Pair (replace r v t) (replace s v t)
replace (Fst r) v s = Fst (replace r v s)
replace (Snd r) v s = Snd (replace r v s)
replace c@(Constant _) _ _ = c

eval :: QuesExpr -> QuesExpr
eval (App (Lambda v _ t) t') = eval (replace t v (eval t'))
eval (App t t') = case t of
  Constant Plus2 ->
    let Constant (C.Num x) = t'
    in Constant (Plus1 x)
  Constant (Plus1 x) ->
    let Constant (C.Num y) = t'
    in Constant (C.Num (x+y))
  _ -> eval (App (eval t) (eval t'))
eval (Let (v, _, t) t') = eval (replace t' v (eval t))
eval (Pair r s) = Pair (eval r) (eval s)
eval (Fst t) = case eval t of
  (Pair r _) -> eval r
  t' -> t'
eval (Snd t) = case eval t of
  (Pair _ s) -> eval s
  t' -> t'
eval t = t
