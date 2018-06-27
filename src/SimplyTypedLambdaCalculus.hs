module SimplyTypedLambdaCalculus where

import Parse

data BaseTy
  = Nat
  deriving (Eq, Show)

data Ty
  = BaseTy BaseTy
  | Arrow Ty Ty
  deriving (Eq, Show)

data Constant
  = Num Int
  | Plus2
  | Plus1 Int
  deriving (Eq, Show)

data Term
  = Var Char (Maybe Ty)
  | Constant Constant
  | Lambda Char Ty Term
  | App Term Term
  deriving (Eq, Show)

data AnnTerm
  = AnnVar Char Ty
  | AnnConstant Constant Ty
  | AnnLambda Char AnnTerm Ty
  | AnnApp AnnTerm AnnTerm Ty
  deriving (Eq, Show)

constType :: Constant -> Ty
constType (SimplyTypedLambdaCalculus.Num _) = BaseTy Nat
constType Plus2 = Arrow (BaseTy Nat) (Arrow (BaseTy Nat) (BaseTy Nat))
constType (Plus1 _) = Arrow (BaseTy Nat) (BaseTy Nat)

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
    annotate' t@(Lambda v' _ t') =
      if v == v' then
        t
      else
        annotate' t'
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

{- Evaling -}

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
      let AnnConstant (SimplyTypedLambdaCalculus.Num x) _ = t'
      in AnnConstant (Plus1 x) (Arrow (BaseTy Nat) (BaseTy Nat))
    AnnConstant (Plus1 x) _ ->
      let AnnConstant (SimplyTypedLambdaCalculus.Num y) _ = t'
      in AnnConstant (SimplyTypedLambdaCalculus.Num (x+y)) (BaseTy Nat)
    _ -> eval (beta (AnnApp (eval t) (eval t') ty))
eval t = t
