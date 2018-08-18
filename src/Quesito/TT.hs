module Quesito.TT where


import Control.Monad (unless, when)
import Data.Bifunctor (first)
import Data.List (find)


type Name = String


data Term v
  = Bound v
  | Free v
  | Type Int
  | Fix
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam Name (Term v)
  deriving (Show, Eq)


data Value
  = VLam Name (Value -> Value)
  | VType Int
  | VPi Name Value (Value -> Value)
  | VNeutral Neutral
  | VDataType Name [Value]
  | VDataCons Name [Value]
  | VCases Name [Value] (Value -> Value)


data Neutral
  = NBound Name  -- used for quotation
  | NFree Name
  | NApp Neutral Value


quote :: Value -> Term Name

quote (VLam x f) =
  Lam x (quote (f (VNeutral (NBound x))))

quote (VCases name args _) =
  Lam "case" (App (foldl (\acc e -> App acc e) (Bound name) (map quote args)) (Bound "case"))

quote (VType i) =
  Type i

quote (VPi x v v') =
  Pi x t t'
  where
    t = quote v
    t' = quote (v' (VNeutral (NBound x)))

quote (VNeutral (NBound x)) =
  Bound x

quote (VNeutral (NFree x)) =
  Free x

quote (VNeutral (NApp n v)) =
  App n' v'
  where
    n' = quote (VNeutral n)
    v' = quote v

quote (VDataType n vs') =
  quote (VDataCons n vs')

quote (VDataCons n vs') =
  quoteCons vs'
  where
    quoteCons :: [Value] -> Term Name
    quoteCons [] =
      Bound n
    quoteCons (v : vs) =
      App (quoteCons vs) (quote v)


data DeBruijnVar = Index Int | DBFree Name
  deriving (Show, Eq)


deBruijnize :: Term Name -> Term DeBruijnVar
deBruijnize =
  deBruijnize' []
  where
    deBruijnize' :: [Name] -> Term Name -> Term DeBruijnVar
    deBruijnize' vars (Bound v) =
      case takeWhile (\v' -> v /= v') vars of
        [] ->
          Bound (DBFree v)
        xs ->
          Bound (Index (length xs))
    deBruijnize' _ (Free v) =
      Free (DBFree v)
    deBruijnize' vars (Pi n t t') =
      Pi "" (deBruijnize' vars t) (deBruijnize' (n : vars) t')
    deBruijnize' vars (Lam n t) =
      Lam "" (deBruijnize' (n : vars) t)
    deBruijnize' _ (Type i) =
      Type i
    deBruijnize' _ Fix =
      Fix
    deBruijnize' vars (App t t') =
      App (deBruijnize' vars t) (deBruijnize' vars t')
    deBruijnize' vars (Ann t t') =
      Ann (deBruijnize' vars t) (deBruijnize' vars t')


data Def term ty
  = DExpr term ty
  | DDataType ty
  | DDataCons ty
  | DCases (Term Name)


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
      )

  | otherwise =
    VLam ""
      (\case_ -> cases arity name p correspondence (case_:cases_))


eval :: Env -> VContext -> Term Name -> Value

eval env ctx (Bound x) =
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
            findNameCons :: Term Name -> Name
            findNameCons cons =
              let (App (Bound "P") e) = snd $ last $ flattenPi cons
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

eval _ _ (Free x) =
  VNeutral (NFree x)

eval _ _ (Type lvl) =
  VType lvl

eval env ctx Fix =
  VLam "" (\a -> VLam "" (\(VLam _ f) ->
                            f (case (case eval env ctx Fix of VLam _ f' -> f') a of VLam _ f' -> f' (VLam "" f))))

eval env ctx (Pi x e e') =
  VPi x (eval env ctx e) (\t -> eval env ((x, t) : ctx) e')

eval env ctx (App e e') =
  let
    t' = eval env ctx e'
  in
    case eval env ctx e of
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

eval env ctx (Ann e _) =
  eval env ctx e

eval env ctx (Lam x e) =
  VLam x (\v -> eval env ((x, v) : ctx) e)


-- * Type inference and checking


type Result a =
  Either String a


typeInf :: Env -> TContext -> Term Name -> Result Value

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
          return (eval env [] ty)

        Nothing ->
          Left ("Free variable: " ++ x)

typeInf env ctx (Free x) =
  typeInf env ctx (Bound x)

typeInf _ _ (Type i) =
  Right (VType (i + 1))

typeInf _ _ Fix =
  Right (VPi "a" (VType 0) (\a -> VPi "" (VPi "" a (const a)) (const a)))

typeInf env ctx (Pi x e e') = do
  t <- typeInf env ctx e
  case t of
    VType i -> do
      t' <-
        typeInf
          env
          ((x, eval env [] e) : ctx)
          (subst x (Free x) e')
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
      return (t' (eval env [] e'))

    _ ->
      Left ("Applying to non-function: " ++ show (quote s))

typeInf env ctx (Ann e ty) = do
  tyTy <- typeInf env ctx ty
  case tyTy of
    VType _ -> do
      let ty' = eval env [] ty
      typeCheck env ctx e ty'
      return ty'

    _ ->
      Left ""

typeInf _ _ e@(Lam _ _) =
  Left ("Can't infer type of lambda expression " ++ show e)


typeCheck :: Env -> TContext -> Term Name -> Value -> Result ()

typeCheck env ctx (Lam x e) (VPi _ t t') =
  typeCheck env ((x, t) : ctx) e (t' (VNeutral (NBound x)))

typeCheck _ _ (Lam _ _) _ =
  Left "6"

typeCheck env ctx t ty = do
  ty' <- typeInf env ctx t
  unless
    (deBruijnize (quote ty) == deBruijnize (quote ty'))
    (Left ("Type mismatch: " ++ show (quote ty) ++ ", " ++ show (quote ty')))


subst :: Name -> Term Name -> Term Name -> Term Name

subst name term (Bound name') =
  if name == name' then
    term
  else
    Bound name'

subst _ _ (Free name') =
  Free name'

subst _ _ (Type level) =
  Type level

subst _ _ Fix =
  Fix

subst name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (subst name term t) (subst name term t')

subst name term (App t t') =
  App (subst name term t) (subst name term t')

subst name term (Ann t t') =
  Ann (subst name term t) (subst name term t')

subst name term (Lam name' t) =
  if name == name' then
    Lam name' t
  else
    Lam name' (subst name term t)


-- * Declarations


data Decl
  = ExprDecl Name (Term Name) (Term Name)
  | TypeDecl
      Name
      (Term Name)  -- ^ Type
      [(Name, Term Name)]  -- ^ Constructors
  deriving Show


checkDecl :: [(Name, Def Value Value)] -> Decl -> Result [(Name, Def Value Value)]

checkDecl env (ExprDecl name expr ty) = do
  tyTy <-
    first
      (\err -> "Type error while checking " ++ name ++ ": " ++ err)
      (typeInf env [] ty)

  case tyTy of
    VType _ -> do
      let ty' = eval env [] ty
      typeCheck env [] expr ty'
      return [(name, DExpr (eval env [] expr) ty')]

    _ ->
      Left (name ++ "'s type is not of kind Type.")

checkDecl env (TypeDecl name ty conss) = do
  tyTy <- typeInf env [] ty
  case tyTy of
    VType _ ->
      case getReturnType ty of
        Type 0 -> do
          let typeDef = (name, DDataType (eval env [] ty))
          conss' <- mapM (uncurry (checkCons typeDef)) conss
          return (typeDef : conss' ++ [(name ++ "-cases", DCases (genCases name ty conss))])

        _ ->
          Left (name ++ " is not a ground type.")

    _ ->
      Left (name ++ "'s type is not of kind Type.")
  where
    getReturnType :: Term Name -> Term Name
    getReturnType (Pi _ _ x) =
      getReturnType x
    getReturnType x =
      x

    isConsOf :: Term Name -> Term Name -> Bool
    isConsOf (App e _) (Pi _ _ t) =
      isConsOf e t
    isConsOf (Bound name') (Type 0) | name == name' =
      True
    isConsOf _ _ =
      False

    checkCons :: (Name, Def Value Value) -> Name -> Term Name -> Result (Name, Def Value Value)
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
      return (name', DDataCons (eval env' [] consTy))


flattenPi :: Term Name -> [(Name, Term Name)]

flattenPi (Pi v e e') =
  (v, e) : flattenPi e'

flattenPi e =
  [("", e)]


unflattenPi :: [(Name, Term Name)] -> Term Name

unflattenPi [] =
  undefined

unflattenPi ((_, e) : []) =
  e

unflattenPi ((v, e) : es) =
  Pi v e (unflattenPi es)


genCases :: Name -> Term Name -> [(Name, Term Name)] -> Term Name

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

    renameAll :: [(Name, Term Name)] -> [(Name, Term Name)]
    renameAll =
      renameAll' 0 []
      where
        renameAll' :: Int -> [(Name, Name)] -> [(Name, Term Name)] -> [(Name, Term Name)]
        renameAll' _ _ [] =
          []
        renameAll' i substs ((v, e) : es) =
          ("x" ++ show i
          , foldl
              (\e' (from, to) -> subst from (Bound to) e')
              e
              substs
          )
            : renameAll' (i + 1) ((v, "x" ++ show i) : substs) es

    addEnd :: Name -> Name -> [(Name, Term Name)] -> [(Name, Term Name)]
    addEnd consName endName args' =
        let args = init args'
        in
        args
        ++ [( ""
            , App
                (Bound endName)
                (foldl
                  (\e (v, _) ->
                    App e (Bound v)
                  )
                  (Bound consName)
                  args
                )
            )
            ]

    addTypeCons :: Name -> Name -> [(Name, Term Name)] -> [(Name, Term Name)]
    addTypeCons typeName endName args' =
      let args = init args'
      in
        args
        ++ [ ( "uniqueName"
              , foldl
                  (\e (v, _) ->
                    App e (Bound v)
                  )
                  (Bound typeName)
                  args
              )
          , ("", App (Bound endName) (Bound "uniqueName"))
          ]
