module Quesito.Eval where

import Quesito.AnnTerm
import Quesito.Constant
import Quesito.Type

replace :: AnnTerm -> Char -> AnnTerm -> AnnTerm
replace t@(AnnVar x _) v t' = if x == v then t' else t
replace t@(AnnLambda x s ty) v t' =
  if x == v then
    t
  else
    AnnLambda x (replace s v t') ty
replace (AnnApp t t' ty) v t'' = AnnApp (replace t v t'') (replace t' v t'') ty
replace t _ _ = t

beta :: AnnTerm -> AnnTerm
beta (AnnApp (AnnLambda v t _) t' _) = replace t v t'
beta (AnnApp t t' ty) = AnnApp (beta t) (beta t') ty
beta t = t

eval :: AnnTerm -> AnnTerm
eval (AnnApp t t' ty) = case t of
    AnnConstant Plus2 _ ->
      let AnnConstant (Quesito.Constant.Num x) _ = t'
      in AnnConstant (Plus1 x) (Arrow (BaseTy Nat) (BaseTy Nat))
    AnnConstant (Plus1 x) _ ->
      let AnnConstant (Quesito.Constant.Num y) _ = t'
      in AnnConstant (Quesito.Constant.Num (x+y)) (BaseTy Nat)
    _ -> eval (beta (AnnApp (eval t) (eval t') ty))
eval t = t