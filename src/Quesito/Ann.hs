module Quesito.Ann where

import Quesito (PPrint(..))
import Quesito.Ann.UnifyM (Subs)
import Quesito.TT (AttrLit(..), BinOp(..), UnOp(..), Flags)
import Quesito.Env (Definition(..))
import qualified Quesito.TT as TT
import qualified Quesito.Marked as Marked
import qualified Quesito.Marked.Mark as Marked

data Term
  = Local String Type AttrLit
  | Hole Int Type
  | Global String Type
  | BaseType Int
  | UniquenessAttr
  | AttrLit AttrLit
  -- | Type Int AttrLit
  | Type
      Int  -- ^ universe
      Term  -- ^ uniqueness attribute
  | Attr Type Term
  | BytesType Int
  | BinOp BinOp
  | UnOp UnOp
  | Num
      Int -- ^ literal
      Int -- ^ bytes
  | Pi String Type Type
  | App Term Term
  | Lam String Type Term
  deriving (Show, Eq)

type Type = Term

instance PPrint Term where
  pprint = pprint . Marked.unmark . downgrade

data Def
  = PatternMatchingDef
      String  -- ^ name
      [([(String, Type)], [Pattern], Term)]  -- ^ equations
      Type  -- ^ type
      Flags
  | TypeDef
      String  -- ^ name
      Type  -- ^ type
      [(String, Term)]  -- ^ constructors
  | ExternDef String Term Flags
  deriving Show

instance Definition Def where
  getNames (PatternMatchingDef n _ _ _) =
    [n]
  getNames (TypeDef n _ conss) =
    n : map fst conss
  getNames (ExternDef name _ _) =
    [name]

fillHoles :: Subs Term -> Def -> Def
fillHoles subs (PatternMatchingDef name equations ty flags) =
  PatternMatchingDef
    name
    (map (\(ctx, lhs, rhs) -> (ctx, lhs, substHoles subs rhs)) equations)
    (substHoles subs ty)
    flags
fillHoles subs (TypeDef name ty conss) =
  TypeDef
    name
    (substHoles subs ty)
    (map (\(name, consTy) -> (name, substHoles subs consTy)) conss)
fillHoles subs (ExternDef name ty flags) =
  ExternDef name (substHoles subs ty) flags

data PatternG t
  = Binding String t
  | Inaccessible t
  | NumPat Int Int
  | NumSucc (PatternG t)
  | Constructor String
  | PatApp (PatternG t) (PatternG t)
  deriving Show

type Pattern = PatternG Term

flattenPatApp :: PatternG a -> [PatternG a]
flattenPatApp (PatApp r s) =
  flattenPatApp r ++ [s]
flattenPatApp t =
  [t]

downgrade :: Term -> Marked.Term
downgrade (Local v _ u) =
  Marked.Local v u
downgrade (Hole _ _) =
  Marked.Hole
downgrade (Global v _) =
  Marked.Global v
downgrade (BaseType i) =
  Marked.BaseType i
downgrade UniquenessAttr =
  Marked.UniquenessAttr
downgrade (AttrLit u) =
  Marked.AttrLit u
downgrade (Type n u) =
  Marked.Type n $ downgrade u
downgrade (Attr ty u) =
  Marked.Attr (downgrade ty) (downgrade u)
downgrade (BytesType n) =
  Marked.BytesType n
downgrade (BinOp op) =
  Marked.BinOp op
downgrade (UnOp op) =
  Marked.UnOp op
downgrade (Num n _) =
  Marked.Num n
downgrade (Pi v s t) =
  Marked.Pi v (downgrade s) (downgrade t)
downgrade (App s t) =
  Marked.App (downgrade s) (downgrade t)
downgrade (Lam v _ t) =
  Marked.Lam v (downgrade t)

typeInf :: Term -> Type
typeInf (Local _ ty _) =
  ty
typeInf (Hole _ ty) =
  ty
typeInf (Global _ ty) =
  ty
typeInf (Type i _) =
  Type (i+1) undefined
typeInf (BytesType _) =
  BaseType 0
typeInf UniquenessAttr =
  BaseType 0  -- Type 0 ?
typeInf (BaseType i) =
  BaseType (i+1)
typeInf (AttrLit UniqueAttr) =
  UniquenessAttr
typeInf (AttrLit SharedAttr) =
  UniquenessAttr
typeInf (Attr t u) =
  case typeInf t of
    BaseType i ->
      Type i u
    _ ->
      error ""
typeInf (BinOp _) =
  Pi "" (BytesType 4) $ Pi "" (BytesType 4) (BytesType 4)
typeInf (UnOp _) =
  Pi "" (BytesType 4) (BytesType 4)
typeInf (Num n b) =
  BytesType b
typeInf (Pi v ty1 ty2) =
  case (typeInf ty1, typeInf ty2) of
    (Type i _, Type j _) ->
      BaseType $ max i j
    _ ->
      error ""
typeInf (App r s) =
  case typeInf r of
    Attr (Pi v ty1 ty2) _ ->
      substLocal v s ty2
    _ ->
      error ""
typeInf (Lam v ty t) =
  Pi v ty $ typeInf t

substHoles :: Subs Term -> Term -> Term
substHoles hs (Hole h' ty) =
  case lookup h' hs of
    Just term ->
      term
    Nothing ->
      Hole h' (substHoles hs ty)
substHoles hs (Local name ty u) =
    Local name (substHoles hs ty) u
substHoles hs (Global name' ty) =
  Global name' (substHoles hs ty)
substHoles hs (Pi name' t t') =
  Pi name' (substHoles hs t) (substHoles hs t')
substHoles hs (App t t') =
  App (substHoles hs t) (substHoles hs t')
substHoles hs (Lam name' ty t) =
  Lam name' (substHoles hs ty) (substHoles hs t)
substHoles hs (Attr ty u) =
  Attr (substHoles hs ty) (substHoles hs u)
substHoles hs (Type i u) =
  Type i $ substHoles hs u
substHoles _ t@(BaseType _) = t
substHoles _ t@UniquenessAttr = t
substHoles _ t@(AttrLit _) = t
substHoles _ t@(BytesType _) = t
substHoles _ t@(BinOp _) = t
substHoles _ t@(UnOp _) = t
substHoles _ t@(Num _ _) = t

substLocal :: String -> Term -> Term -> Term
substLocal name term (Local name' ty u) =
  if name == name' then
    term
  else
    Local name' ty u
substLocal _ _ (Global name' ty) =
  Global name' ty
substLocal name term (Pi name' t t') =
  if name == name' then
    Pi name' t t'
  else
    Pi name' (substLocal name term t) (substLocal name term t')
substLocal name term (App t t') =
  App (substLocal name term t) (substLocal name term t')
substLocal name term (Lam name' ty t) =
  if name == name' then
    Lam name' ty t
  else
    Lam name' (substLocal name term ty) (substLocal name term t)
substLocal name term (Attr ty u) =
  Attr (substLocal name term ty) (substLocal name term u)
substLocal name term (Type i u) =
  Type i $ substLocal name term u
substLocal _ _ t@(BaseType _) = t
substLocal _ _ t@UniquenessAttr = t
substLocal _ _ t@(AttrLit _) = t
substLocal _ _ t@(BytesType _) = t
substLocal _ _ t@(BinOp _) = t
substLocal _ _ t@(UnOp _) = t
substLocal _ _ t@(Num _ _) = t

substGlobal :: String -> Term -> Term -> Term
substGlobal name term (Global name' ty) =
  if name == name' then
    term
  else
    Global name' ty
substGlobal _ _ (Local name' ty u) =
  Local name' ty u
substGlobal name term (Pi name' t t') =
  Pi name' (substGlobal name term t) (substGlobal name term t')
substGlobal name term (App t t') =
  App (substGlobal name term t) (substGlobal name term t')
substGlobal name term (Lam name' ty t) =
  Lam name' (substGlobal name term ty) (substGlobal name term t)
substGlobal _ _ t =
  t

flattenApp :: Term -> [Term]
flattenApp =
  flattenApp' []
  where
    flattenApp' :: [Term] -> Term -> [Term]
    flattenApp' as (App f a) =
      flattenApp' (a:as) f
    flattenApp' as f =
      f:as

flattenPi :: Type -> ([Type], Type)
flattenPi (Pi _ ty1 ty2) =
  let (args, ret) = flattenPi ty2
  in (ty1 : args, ret)
flattenPi t =
  ([], t)
