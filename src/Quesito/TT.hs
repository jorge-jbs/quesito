{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Quesito.TT where


import Prelude hiding (print)
import Control.Monad (unless, when)
import Data.Bifunctor (first)
import Data.List (find)


class Printable a where
  print :: a -> String


type Name = String


instance Printable Name where
  print n =
    n


data TermKind v
  = Bound v
  | Free v
  | Type Int
  | Fix
  | Pi Name (Term v) (Term v)
  | App (Term v) (Term v)
  | Ann (Term v) (Term v)
  | Lam Name (Term v)
  deriving Eq


data Pos
  = Pos
      Int  -- ^ line
      Int  -- ^ column
  | None
  deriving Eq


instance Show Pos where
  show (Pos y x) =
    "line " ++ show y ++ " and column " ++ show x
  show None =
    "MISSING"


data Term v = Term Pos (TermKind v)


instance Printable v => Show (TermKind v) where
  show (Bound v) =
    print v

  show (Free v) =
    print v

  show (Type i) =
    "(" ++ "Type " ++ show i ++ ")"

  show Fix =
    "fix"

  show (Pi "" t t') =
    "(" ++ show t ++ " -> " ++ show t' ++ ")"

  show (Pi n t t') =
    "(" ++ "(" ++ n ++ " : "++ show t ++ ") -> " ++ show t' ++ ")"

  show (App t t') =
    "(" ++ show t ++ " " ++ show t' ++ ")"

  show (Ann t t') =
    "(" ++ show t ++ " " ++ show t' ++ ")"

  show (Lam n t) =
    "(" ++ "\\" ++ n ++ " -> " ++ show t ++ ")"


instance Printable v => Show (Term v) where
  show (Term _ k) =
    show k


instance Eq v => Eq (Term v) where
  Term _ t == Term _ t' =
    t == t'


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
  Term None (Lam x (quote (f (VNeutral (NBound x)))))

quote (VCases name args _) =
  Term None (Lam "case" (Term None (App (foldl (\acc e -> Term None (App acc e)) (Term None (Bound name)) (map quote args)) (Term None (Bound "case")))))

quote (VType i) =
  Term None (Type i)

quote (VPi x v v') =
  Term None (Pi x t t')
  where
    t = quote v
    t' = quote (v' (VNeutral (NBound x)))

quote (VNeutral (NBound x)) =
  Term None (Bound x)

quote (VNeutral (NFree x)) =
  Term None (Free x)

quote (VNeutral (NApp n v)) =
  Term None (App n' v')
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
      Term None (Bound n)
    quoteCons (v : vs) =
      Term None (App (quoteCons vs) (quote v))


data DeBruijnVar = Index Int | DBFree Name
  deriving Eq


deBruijnize :: Term Name -> Term DeBruijnVar
deBruijnize =
  deBruijnize' []
  where
    deBruijnize' :: [Name] -> Term Name -> Term DeBruijnVar
    deBruijnize' vars (Term pos k) =
      case k of
        Bound v ->
          case takeWhile (\v' -> v /= v') vars of
            [] ->
              Term pos (Bound (DBFree v))
            xs ->
              Term pos (Bound (Index (length xs)))
        Free v ->
          Term pos (Free (DBFree v))
        Pi n t t' ->
          Term pos (Pi "" (deBruijnize' vars t) (deBruijnize' (n : vars) t'))
        Lam n t ->
          Term pos (Lam "" (deBruijnize' (n : vars) t))
        Type i ->
          Term pos (Type i)
        Fix ->
          Term pos (Fix)
        App t t' ->
          Term pos (App (deBruijnize' vars t) (deBruijnize' vars t'))
        Ann t t' ->
          Term pos (Ann (deBruijnize' vars t) (deBruijnize' vars t'))


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
eval env ctx (Term pos k) =
  case k of
    Bound x ->
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
                  let (Term _ (App (Term _ (Bound "P")) e)) = snd $ last $ flattenPi cons
                  in findNameCons' e
                  where
                    findNameCons' (Term _ (App e' _)) =
                      findNameCons' e'
                    findNameCons' (Term _ (Bound e')) =
                      e'
                    findNameCons' _ =
                      undefined
              in
                VLam "P"
                  (\p ->
                      cases (length cases_) x p (zip (map (findNameCons . snd) cases_) [0..]) []
                  )

            Nothing ->
              error ("Found free variable at " ++ show pos ++ ": " ++ x)

    Free x ->
      VNeutral (NFree x)

    Type lvl ->
      VType lvl

    Fix ->
      VLam "" (\a -> VLam "" (\(VLam _ f) ->
                                f (case (case eval env ctx (Term pos Fix) of VLam _ f' -> f') a of VLam _ f' -> f' (VLam "" f))))

    Pi x e e' ->
      VPi x (eval env ctx e) (\t -> eval env ((x, t) : ctx) e')

    App e e' ->
      let
        !t' = eval env ctx e'
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
            error ("Application to non-function at " ++ show pos ++ ": " ++ show (quote x))

    Ann e _ ->
      eval env ctx e

    Lam x e ->
      VLam x (\v -> eval env ((x, v) : ctx) e)


-- * Type inference and checking


type Result a =
  Either String a


typeInf :: Env -> TContext -> Term Name -> Result Value
typeInf env ctx (Term pos k) =
  case k of
    Bound x ->
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
              Left ("Free variable at " ++ show pos ++ ": " ++ x)

    Free x ->
      typeInf env ctx (Term pos (Bound x))

    Type i ->
      Right (VType (i + 1))

    Fix ->
      Right (VPi "a" (VType 0) (\a -> VPi "" (VPi "" a (const a)) (const a)))

    Pi x e e' -> do
      t <- typeInf env ctx e
      case t of
        VType i -> do
          t' <-
            typeInf
              env
              ((x, eval env [] e) : ctx)
              (subst x (Term pos (Free x)) e')
          case t' of
            VType j ->
              return (VType (max i j))

            _ ->
              Left ("1: " ++ show pos)

        _ ->
          Left ("2: " ++ show pos)

    App e e' -> do
      s <- typeInf env ctx e
      case s of
        VPi _ t t' -> do
          typeCheck env ctx e' t
          return (t' (eval env [] e'))

        _ ->
          Left ("Applying to non-function at " ++ show pos ++ ": " ++ show (quote s))

    Ann e ty -> do
      tyTy <- typeInf env ctx ty
      case tyTy of
        VType _ -> do
          let ty' = eval env [] ty
          typeCheck env ctx e ty'
          return ty'

        _ ->
          Left ""

    e@(Lam _ _) ->
      Left ("Can't infer type of lambda expression " ++ show e)


typeCheck :: Env -> TContext -> Term Name -> Value -> Result ()

typeCheck env ctx (Term _ (Lam x e)) (VPi _ t t') =
  typeCheck env ((x, t) : ctx) (subst x (Term None (Free x)) e) (t' (VNeutral (NBound x)))

typeCheck _ _ (Term pos (Lam _ _)) _ =
  Left ("6: " ++ show pos)

typeCheck env ctx t@(Term pos _) ty = do
  ty' <- typeInf env ctx t
  unless
    (deBruijnize (quote ty) == deBruijnize (quote ty'))
    (Left ("Type mismatch at " ++ show pos ++ ". Expected " ++ show (quote ty) ++ " and got " ++ show (quote ty')))


subst :: Name -> Term Name -> Term Name -> Term Name
subst name term (Term pos k) =
  case k of
    Bound name' ->
      if name == name' then
        term
      else
        Term pos (Bound name')

    Free name' ->
      Term pos (Free name')

    Type level ->
      Term pos (Type level)

    Fix ->
      Term pos Fix

    Pi name' t t' ->
      if name == name' then
        Term pos (Pi name' t t')
      else
        Term pos (Pi name' (subst name term t) (subst name term t'))

    App t t' ->
      Term pos (App (subst name term t) (subst name term t'))

    Ann t t' ->
      Term pos (Ann (subst name term t) (subst name term t'))

    Lam name' t ->
      if name == name' then
        Term pos (Lam name' t)
      else
        Term pos (Lam name' (subst name term t))


-- * Declarations


data Decl
  = ExprDecl Name (Term Name) (Term Name)
  | TypeDecl
      Name
      (Term Name)  -- ^ Type
      [(Name, Term Name)]  -- ^ Constructors


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
        Term _ (Type 0) -> do
          let typeDef = (name, DDataType (eval env [] ty))
          conss' <- mapM (uncurry (checkCons typeDef)) conss
          return (typeDef : conss' ++ [(name ++ "-cases", DCases (genCases name ty conss))])

        _ ->
          Left (name ++ " is not a ground type.")

    _ ->
      Left (name ++ "'s type is not of kind Type.")
  where
    getReturnType :: Term Name -> Term Name
    getReturnType (Term _ (Pi _ _ x)) =
      getReturnType x
    getReturnType x =
      x

    isConsOf :: Term Name -> Term Name -> Bool
    isConsOf (Term _ (App e _)) (Term _ (Pi _ _ t)) =
      isConsOf e t
    isConsOf (Term _ (Bound name')) (Term _ (Type 0)) | name == name' =
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

flattenPi (Term _ (Pi v e e')) =
  (v, e) : flattenPi e'

flattenPi e =
  [("", e)]


unflattenPi :: [(Name, Term Name)] -> Term Name

unflattenPi [] =
  undefined

unflattenPi ((_, e) : []) =
  e

unflattenPi ((v, e) : es) =
  Term None (Pi v e (unflattenPi es))


genCases :: Name -> Term Name -> [(Name, Term Name)] -> Term Name

genCases name ty conss =
  Term
    None
    (Pi
      "P"
      (unflattenPi
        ((init $ addTypeCons name "" $ renameAll $ flattenPi $ ty)
          ++ [("", Term None (Type 0))]
        )
      )
      (foldr
        (\a b -> Term None (Pi "" a b))
        (unflattenPi $ addTypeCons name "P" $ renameAll $ flattenPi ty)
        conss'
      )
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
              (\e' (from, to) -> subst from (Term None (Bound to)) e')
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
            , Term
                None
                (App
                  (Term None (Bound endName))
                  (foldl
                    (\e (v, _) ->
                      Term None (App e (Term None (Bound v)))
                    )
                    (Term None (Bound consName))
                    args
                  )
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
                    Term None (App e (Term None (Bound v)))
                  )
                  (Term None (Bound typeName))
                  args
              )
          , ("", Term None (App (Term None (Bound endName)) (Term None (Bound "uniqueName"))))
          ]
