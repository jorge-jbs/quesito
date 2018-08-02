module Quesito.TT where


import Data.List (find)


import Control.Monad (unless)


type Name = String


-- | Inferable terms
data InfTerm
  = Var Name
  | Type Int
  | Pi Name InfTerm InfTerm
  | App InfTerm CheckTerm
  | Ann CheckTerm InfTerm
  | Constant Const
  deriving (Show, Eq)


data Const
  = IntType
  | Int Int
  | Plus
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
  | VIntType
  | VInt Int
  | VDataType Name
  | VDataCons Name [Value]


data Neutral
  = NVar Name  -- used for quotation
  | NApp Neutral Value


quote :: Value -> CheckTerm

quote (VLam x f) =
  Lam x (quote (f (VNeutral (NVar x))))

quote (VType i) =
  Inf (Type i)

quote (VPi x v v') =
  Inf (Pi x t t')
  where
    Inf t = quote v
    Inf t' = quote (v' (VNeutral (NVar x)))

quote (VNeutral (NVar x)) =
  Inf (Var x)

quote (VNeutral (NApp n v)) =
  Inf (App n' v')
  where
    Inf n' = quote (VNeutral n)
    v' = quote v

quote VIntType =
  Inf (Constant IntType)

quote (VInt n) =
  Inf (Constant (Int n))

quote (VDataType n) =
  Inf (Var n)

quote (VDataCons n vs') =
  Inf (quoteCons vs')
  where
    quoteCons :: [Value] -> InfTerm

    quoteCons [] =
      Var n

    quoteCons (v : vs) =
      App (quoteCons vs) (quote v)


data Def term ty
  = DExpr term ty
  | DDataType ty
  | DDataCons ty


type Result a =
  Either String a


type TContext =
  [(Name, Value)]


type VContext =
  TContext


type Env =
  [(Name, Def Value Value)]


evalInf :: Env -> VContext -> InfTerm -> Value

evalInf env ctx (Var x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      v

    Nothing ->
      case snd <$> find ((==) x . fst) env of
        Just (DExpr v _) ->
          v

        Just (DDataType _) ->
          VDataType x

        Just (DDataCons _) ->
          VDataCons x []

        Nothing ->
          error ("Found free variable: " ++ x)

evalInf _ _ (Type lvl) =
  VType lvl

evalInf env ctx (Pi x e e') =
  VPi x (evalInf env ctx e) (\t -> evalInf env ((x, t) : ctx) e')

evalInf env ctx (App e e') =
  let
    t' = evalCheck env ctx e'
  in
    case evalInf env ctx e of
      VLam _ t ->
        t t'

      VDataCons n ts ->
        VDataCons n (t' : ts)

      _ ->
        error "Application to non-function."

evalInf env ctx (Ann e _) =
  evalCheck env ctx e

evalInf _ _ (Constant IntType) =
  VIntType

evalInf _ _ (Constant (Int n)) =
  VInt n

evalInf _ _ (Constant Plus) =
  VLam "x" (\(VInt x) -> VLam "y" (\(VInt y) -> VInt (x + y)))


evalCheck :: Env -> VContext -> CheckTerm -> Value

evalCheck env ctx (Inf e) =
  evalInf env ctx e

evalCheck env ctx (Lam x e) =
  VLam x (\v -> evalCheck env ((x, v) : ctx) e)


typeInf :: Env -> TContext -> InfTerm -> Result Value

typeInf env ctx (Var x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      return v

    Nothing ->
      case snd <$> find ((==) x . fst) env of
        Just (DExpr _ ty) ->
          return ty

        Just (DDataType ty) ->
          return ty

        Just (DDataCons ty) ->
          return ty

        Nothing ->
          error ("Found free variable: " ++ x)

typeInf _ _ (Type i) =
  Right (VType (i + 1))

typeInf env ctx (Pi x e e') = do
  t <- typeInf env ctx e
  case t of
    VType i -> do
      t' <- typeInf env ((x, t) : ctx) e'
      case t' of
        VType j ->
          return (VType (max i j))

        _ ->
          Left "1"

    _ ->
      Left "2"

typeInf env ctx (App e e') = do
  s <- typeInf env ctx e
  case s of
    VPi _ t t' -> do
      typeCheck env ctx e' t
      return (t' (evalCheck env [] e'))

    _ ->
      Left ("Applying to non-function: " ++ show (quote s))

typeInf env ctx (Ann e ty) = do
  tyTy <- typeInf env ctx ty
  case tyTy of
    VType _ -> do
      let ty' = evalInf env [] ty
      typeCheck env ctx e ty'
      return ty'

    _ ->
      Left ""

typeInf _ _ (Constant IntType) =
  return (VType 0)

typeInf _ _ (Constant (Int _)) =
  return VIntType

typeInf _ _ (Constant Plus) =
  return (VPi "" VIntType (const (VPi "" VIntType (const VIntType))))


typeCheck :: Env -> TContext -> CheckTerm -> Value -> Result ()
typeCheck env ctx (Lam x e) (VPi _ t t') =
  typeCheck env ((x, t) : ctx) e (t' (VNeutral (NVar x)))

typeCheck _ _ (Lam _ _) _ =
  Left "6"

typeCheck env ctx (Inf t) ty = do
  ty' <- typeInf env ctx t
  unless
    (quote ty == quote ty')
    (Left ("Type mismatch: " ++ show (quote ty) ++ ", " ++ show (quote ty')))
