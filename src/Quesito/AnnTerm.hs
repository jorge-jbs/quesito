module Quesito.AnnTerm where

import Quesito.Constant
import Quesito.Term
import Quesito.Type

data AnnTerm
  = AnnVar Char Ty
  | AnnConstant Constant Ty
  | AnnLambda Char AnnTerm Ty
  | AnnApp AnnTerm AnnTerm Ty
  deriving (Eq, Show)

annotatedType :: AnnTerm -> Ty
annotatedType (AnnVar _ ty) = ty
annotatedType (AnnConstant _ ty) = ty
annotatedType (AnnLambda _ _ ty) = ty
annotatedType (AnnApp _ _ ty) = ty

annotate :: Term -> Maybe AnnTerm
annotate (Var v ty) = AnnVar v <$> ty
annotate (Constant c) = Just (AnnConstant c (constType c))
annotate (Lambda v ty t) = do
  t' <- annotate (annotate' t)
  let ty' = annotatedType t'
  return (AnnLambda v t' (Arrow ty ty'))
  where
    annotate' :: Term -> Term
    annotate' (Var v' _) = Var v' (Just ty)
    annotate' t@(Lambda v' ty t') =
      if v == v' then
        t
      else
        Lambda v' ty (annotate' t')
    annotate' (App t t') = App (annotate' t) (annotate' t')
    annotate' t = t
annotate (App t t') = do
  t'' <- annotate t
  t''' <- annotate t'
  let ty = annotatedType t''
  let ty' = annotatedType t'''
  case ty of
    Arrow ty1 ty2 | ty1 == ty' -> Just (AnnApp t'' t''' ty2)
    _ -> Nothing
