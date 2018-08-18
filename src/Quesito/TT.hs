module Quesito.TT where


import Control.Monad (unless, when)
import Data.Bifunctor (first)
import Data.List (find)


type Name = String


-- | Inferable terms
data InfTerm
  = Bound Name
  | Free Name
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
  | VDataType Name [Value]
  | VDataCons Name [Value]
  | VCases Name [Value] (Value -> Value)


data Neutral
  = NBound Name  -- used for quotation
  | NFree Name
  | NApp Neutral Value


quote :: Value -> CheckTerm

quote (VLam x f) =
  Lam x (quote (f (VNeutral (NBound x))))

quote (VCases name args _) =
  Lam "case" (Inf $ App (foldl (\acc e -> App acc e) (Bound name) (map quote args)) (Inf $ Bound "case"))

quote (VType i) =
  Inf (Type i)

quote (VPi x v v') =
  Inf (Pi x t t')
  where
    Inf t = quote v
    Inf t' = quote (v' (VNeutral (NBound x)))

quote (VNeutral (NBound x)) =
  Inf (Bound x)

quote (VNeutral (NFree x)) =
  Inf (Free x)

quote (VNeutral (NApp n v)) =
  Inf (App n' v')
  where
    Inf n' = quote (VNeutral n)
    v' = quote v

quote VIntType =
  Inf (Constant IntType)

quote (VInt n) =
  Inf (Constant (Int n))

quote (VDataType n vs') =
  quote (VDataCons n vs')

quote (VDataCons n vs') =
  Inf (quoteCons vs')
  where
    quoteCons :: [Value] -> InfTerm

    quoteCons [] =
      Bound n

    quoteCons (v : vs) =
      App (quoteCons vs) (quote v)


data Def term ty
  = DExpr term ty
  | DDataType ty
  | DDataCons ty
  | DCases InfTerm


type TContext =
  [(Name, Value)]


type VContext =
  TContext


type Env =
  [(Name, Def Value Value)]


-- * Evaling


cases :: Int -> Name -> Value -> [(Name, Int)] -> [Value] -> Value
cases arity name p correspondence cases_
  | length cases_ == arity =
    VCases name (p : reverse cases_)
      (\cons ->
         case cons of
           VDataCons name' args ->
             let case_ = (reverse cases_) !! (snd $ maybe undefined id $ find ((==) name' . fst) correspondence)
             in foldl (\(VLam _ f) arg-> f arg) case_ args

           x ->
             VNeutral (NApp (foldl (\acc e -> NApp acc e) (NBound name) (p : reverse cases_)) x)

           -- x ->
             -- error ("Parameter is not a constructor: " ++ show (quote x) ++ "; " ++ show arity ++ "; " ++ show correspondence)
      )

  | otherwise =
    VLam ""
      (\case_ -> cases arity name p correspondence (case_:cases_))


evalInf :: Env -> VContext -> InfTerm -> Value

evalInf env ctx (Bound x) =
  case snd <$> find ((==) x . fst) ctx of
    Just v ->
      v

    Nothing ->
      case snd <$> find ((==) x . fst) env of
        Just (DExpr v _) ->
          v

        Just (DDataType _) ->
          VDataType x []

        Just (DDataCons _) ->
          VDataCons x []

        Just (DCases ty) ->
          let
            cases_ = init $ init $ tail $ flattenPi ty
            findNameCons :: InfTerm -> Name
            findNameCons cons =
              let (App (Bound "P") (Inf e)) = snd $ last $ flattenPi cons
              in findNameCons' e
              where
                findNameCons' (App e' _) =
                  findNameCons' e'
                findNameCons' (Bound e') =
                  e'
                findNameCons' _ =
                  undefined
          in
            VLam "P"
              (\p ->
                  cases (length cases_) x p (zip (map (findNameCons . snd) cases_) [0..]) []
              )

        Nothing ->
          error ("Found free variable: " ++ x)

evalInf _ _ (Free x) =
  VNeutral (NFree x)

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

      VDataType n ts ->
        VDataType n (t' : ts)

      VCases _ _ t ->
        t t'

      x ->
        error ("Application to non-function: " ++ show (quote x))

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


-- * Type inference and checking


type Result a =
  Either String a


typeInf :: Env -> TContext -> InfTerm -> Result Value

typeInf env ctx (Bound x) =
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

        Just (DCases ty) ->
          return (evalInf env [] ty)

        Nothing ->
          Left ("Free variable: " ++ x)

typeInf env ctx (Free x) =
  typeInf env ctx (Bound x)

typeInf _ _ (Type i) =
  Right (VType (i + 1))

typeInf env ctx (Pi x e e') = do
  t <- typeInf env ctx e
  case t of
    VType i -> do
      t' <-
        typeInf
          env
          ((x, evalInf env [] e) : ctx)
          (substInf x (Free x) e')
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
  typeCheck env ((x, t) : ctx) e (t' (VNeutral (NBound x)))

typeCheck _ _ (Lam _ _) _ =
  Left "6"

typeCheck env ctx (Inf t) ty = do
  ty' <- typeInf env ctx t
  unless
    (quote ty == quote ty')
    (Left ("Type mismatch: " ++ show (quote ty) ++ ", " ++ show (quote ty')))


substInf :: Name -> InfTerm -> InfTerm -> InfTerm

substInf name term (Bound name') =
  if name == name' then
    term
  else
    Bound name'

substInf _ _ (Free name') =
  Free name'

substInf _ _ (Type level) =
  Type level

substInf name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (substInf name term t) (substInf name term t')

substInf name term (App t t') =
  App (substInf name term t) (substCheck name term t')

substInf name term (Ann t t') =
  Ann (substCheck name term t) (substInf name term t')

substInf _ _ (Constant c) =
  Constant c

substCheck :: Name -> InfTerm -> CheckTerm -> CheckTerm

substCheck name term (Inf t) =
  Inf (substInf name term t)

substCheck name term (Lam name' t) =
  if name == name' then
    Lam name' t
  else
    Lam name' (substCheck name term t)


-- * Declarations


data Decl
  = ExprDecl Name CheckTerm InfTerm
  | TypeDecl
      Name
      InfTerm  -- ^ Type
      [(Name, InfTerm)]  -- ^ Constructors
  deriving Show


checkDecl :: [(Name, Def Value Value)] -> Decl -> Result [(Name, Def Value Value)]

checkDecl env (ExprDecl name expr ty) = do
  tyTy <-
    first
      (\err -> "Type error while checking " ++ name ++ ": " ++ err)
      (typeInf env [] ty)

  case tyTy of
    VType _ -> do
      let ty' = evalInf env [] ty
      typeCheck env [] expr ty'
      return [(name, DExpr (evalCheck env [] expr) ty')]

    _ ->
      Left (name ++ "'s type is not of kind Type.")

checkDecl env (TypeDecl name ty conss) = do
  tyTy <- typeInf env [] ty
  case tyTy of
    VType _ ->
      case getReturnType ty of
        Type 0 -> do
          let typeDef = (name, DDataType (evalInf env [] ty))
          conss' <- mapM (uncurry (checkCons typeDef)) conss
          return (typeDef : conss' ++ [(name ++ "-cases", DCases (genCases name ty conss))])

        _ ->
          Left (name ++ " is not a ground type.")

    _ ->
      Left (name ++ "'s type is not of kind Type.")
  where
    getReturnType :: InfTerm -> InfTerm
    getReturnType (Pi _ _ x) =
      getReturnType x
    getReturnType x =
      x

    isConsOf :: InfTerm -> InfTerm -> Bool
    isConsOf (App e _) (Pi _ _ t) =
      isConsOf e t
    isConsOf (Bound name') (Type 0) | name == name' =
      True
    isConsOf _ _ =
      False

    checkCons :: (Name, Def Value Value) -> Name -> InfTerm -> Result (Name, Def Value Value)
    checkCons typeDef name' consTy = do
      let env' = typeDef : env
      tyTy <-
        first
          (\err -> "Type error while checking " ++ name' ++ ": " ++ err)
          (typeInf env' [] consTy)
      when
        (case tyTy of VType _ -> False; _ -> True)
        (Left (name' ++ "'s type is not of kind Type."))
      when
        (not (isConsOf (getReturnType consTy) ty))
        (Left (name' ++ " is not a constructor for " ++ name ++ "."))
      return (name', DDataCons (evalInf env' [] consTy))


flattenPi :: InfTerm -> [(Name, InfTerm)]

flattenPi (Pi v e e') =
  (v, e) : flattenPi e'

flattenPi e =
  [("", e)]


unflattenPi :: [(Name, InfTerm)] -> InfTerm

unflattenPi [] =
  undefined

unflattenPi ((_, e) : []) =
  e

unflattenPi ((v, e) : es) =
  Pi v e (unflattenPi es)


genCases :: Name -> InfTerm -> [(Name, InfTerm)] -> InfTerm

genCases name ty conss =
  Pi
    "P"
    (unflattenPi
      ((init $ addTypeCons name "" $ renameAll $ flattenPi $ ty)
        ++ [("", Type 0)]
      )
    )
    (foldr
      (Pi "")
      (unflattenPi $ addTypeCons name "P" $ renameAll $ flattenPi ty)
      conss'
    )
  where
    conss' =
      map
        (\(name', cons) ->
            unflattenPi
            $ addEnd name' "P"
            $ renameAll
            $ flattenPi cons
        )
        conss

    renameAll :: [(Name, InfTerm)] -> [(Name, InfTerm)]
    renameAll =
      renameAll' 0 []
      where
        renameAll' :: Int -> [(Name, Name)] -> [(Name, InfTerm)] -> [(Name, InfTerm)]
        renameAll' _ _ [] =
          []
        renameAll' i substs ((v, e) : es) =
          ("x" ++ show i
          , foldl
              (\e' (from, to) -> substInf from (Bound to) e')
              e
              substs
          )
            : renameAll' (i + 1) ((v, "x" ++ show i) : substs) es

    addEnd :: Name -> Name -> [(Name, InfTerm)] -> [(Name, InfTerm)]
    addEnd consName endName args' =
        let args = init args'
        in
        args
        ++ [( ""
            , App
                (Bound endName)
                (Inf $ foldl
                  (\e (v, _) ->
                    App e (Inf (Bound v))
                  )
                  (Bound consName)
                  args
                )
            )
            ]

    addTypeCons :: Name -> Name -> [(Name, InfTerm)] -> [(Name, InfTerm)]
    addTypeCons typeName endName args' =
      let args = init args'
      in
        args
        ++ [ ( "uniqueName"
              , foldl
                  (\e (v, _) ->
                    App e (Inf (Bound v))
                  )
                  (Bound typeName)
                  args
              )
          , ("", App (Bound endName) (Inf (Bound "uniqueName")))
          ]
