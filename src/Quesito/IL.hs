module Quesito.IL where

import Data.List (delete, find, nub)
import Data.Maybe (fromJust)

import Quesito.Constant
import Quesito.QuesExpr as Q hiding (freeVars)
import Quesito.Type

data ILExpr
  = AnnVar Char Ty
  | AnnConstant Constant Ty
  | AnnLambda Char ILExpr Ty
  | AnnApp ILExpr ILExpr Ty
  deriving (Eq, Show)

freeVars :: ILExpr -> [(Char, Ty)]
freeVars (AnnVar v ty) = [(v, ty)]
freeVars (AnnConstant _ _) = []
freeVars (AnnLambda v t (Arrow ty _)) = delete (v, ty) (freeVars t)
freeVars (AnnLambda _ _ _) = undefined
freeVars (AnnApp t t' _) = nub (freeVars t ++ freeVars t')

annotatedType :: ILExpr -> Ty
annotatedType (AnnVar _ ty) = ty
annotatedType (AnnConstant _ ty) = ty
annotatedType (AnnLambda _ _ ty) = ty
annotatedType (AnnApp _ _ ty) = ty

desugar :: QuesExpr -> Maybe ILExpr
desugar = desugar' []
  where
    desugar' :: [(Char, Ty)] -> QuesExpr -> Maybe ILExpr
    desugar' scope (Var v) =
      AnnVar v <$> snd <$> find (\(v', _) -> v == v') scope
    desugar' _ (Constant c) =
      Just (AnnConstant c (constType c))
    desugar' scope (Lambda v ty t) = do
      t' <- desugar' ((v, ty) : scope) t
      return (AnnLambda v t' (Arrow ty (annotatedType t')))
    desugar' scope (App t t') = do
      t_ <- desugar' scope t
      t_' <- desugar' scope t'
      let Arrow _ ty = annotatedType t_
      return (AnnApp t_ t_' ty)
