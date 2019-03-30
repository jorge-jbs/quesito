module Quesito.LLTT where

import Quesito
import Quesito.TT (BinOp(..), UnOp(..))
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env

data Var
  = Local String Type
  | TypeCons String Type
  | Constructor String Type
  | Global String Type
  deriving Show

data Term
  = Constant Var
  | Num
      Int  -- ^ literal
      Int  -- ^ bytes
  | Pi String Type Type
  | Type
  | BytesType Int
  | Call Var [Term] Type
  | BinOp BinOp Term Term
  | UnOp UnOp Term
  deriving Show

type Type = Term

type Env = Env.Env Def

type Pattern = Ann.PatternG Term

lowerPat :: MonadQues m => Env -> Ann.Pattern -> m Pattern
lowerPat env (Ann.Binding v ty) =
  Ann.Binding v <$> lower env ty
lowerPat env (Ann.Inaccessible t) =
  Ann.Inaccessible <$> lower env t
lowerPat _ (Ann.NumPat n b) =
  return $ Ann.NumPat n b
lowerPat _ (Ann.Constructor v) =
  return $ Ann.Constructor v
lowerPat env (Ann.PatApp r s) =
  Ann.PatApp <$> lowerPat env r <*> lowerPat env s

data Def
  = PatternMatchingDef
      String  -- ^ name
      [([(String, Type)], [Pattern], Term)]  -- ^ equations
      Type  -- ^ type
  | TypeDef
      String  -- ^ name
      [([(String, Type)], [Pattern], [Type])]  -- ^ equations
      Type  -- ^ type
  | ConstructorDef
      String  -- ^ constructor name
      Type  -- ^ type name
      Integer  -- ^ tag
  deriving Show

instance Env.Definition Def where
  getNames (PatternMatchingDef n _ _) =
    [n]
  getNames (TypeDef n _ _) =
    [n]
  getNames (ConstructorDef n _ _) =
    [n]

lower :: MonadQues m => Env -> Ann.Term -> m Term
lower env (Ann.Local v ty) =
  Constant . Local v <$> lower env ty
lower env (Ann.Global v ty) =
  case Env.lookup v env of
    Just (TypeDef _ _ _) ->
      Constant . TypeCons v <$> lower env ty
    Just (ConstructorDef _ _ _) ->
      Constant . Constructor v <$> lower env ty
    _ ->
      Constant . Global v <$> lower env ty
lower _ (Ann.Type i) =
  return Type
lower _ (Ann.BytesType i) =
  return $ BytesType i
lower _ (Ann.BinOp op) =
  error ""
lower _ (Ann.UnOp op) =
  error ""
lower _ (Ann.Num n i) =
  return $ Num n i
lower env (Ann.Pi v ty1 ty2) =
  Pi v <$> lower env ty1 <*> lower env ty2
lower env t@(Ann.App _ _) =
  case Ann.flattenApp t of
    [Ann.BinOp op, a, b] ->
      BinOp op <$> lower env a <*> lower env b
    [Ann.UnOp op, a] ->
      UnOp op <$> lower env a
    hd : tl -> do
      hd' <- lower env hd
      tl' <- mapM (lower env) tl
      ty <- lower env $ snd $ Ann.flattenPi $ Ann.typeInf t
      case hd' of
        Constant v ->
          return $ Call v tl' ty
        _ ->
          error ""
    [] ->
      error ""
lower _ (Ann.Lam _ _ _) =
  throwError "Can't generate lambda expressions"

{-
undo :: Term -> Ann.Term
undo (Constant (Local v ty)) =
  Ann.Local v ty
undo (Constant (TypeCons v ty)) =
  Ann.Global v ty
undo (Constant (Constructor v ty)) =
  Ann.Global v ty
undo (Constant (Global v ty)) =
  Ann.Global v ty
undo (Num n b) =
  Ann.Num n b
undo (Pi v ty1 ty2) =
  Ann.Pi v (undo ty1) (undo ty2)
undo (Type i) =
  Ann.Type i
undo (BytesType n) =
  Ann.BytesType n
undo (Call v ts) =
  foldl Ann.App (undo $ Constant v) ts
undo (BinOp op r s) =
  Ann.BinOp op `Ann.App` undo r `Ann.App` undo s
undo (UnOp UnOp Term) =
-}

typeOfVar (Local _ ty) = ty
typeOfVar (TypeCons _ ty) = ty
typeOfVar (Constructor _ ty) = ty
typeOfVar (Global _ ty) = ty

nameOfVar (Local v _) = v
nameOfVar (TypeCons v _) = v
nameOfVar (Constructor v _) = v
nameOfVar (Global v _) = v

typeInf :: Term -> Type
typeInf (Constant v) =
  typeOfVar v
typeInf Type =
  Type
typeInf (BytesType _) =
  Type
typeInf (BinOp _ _ _) =
  BytesType 4
typeInf (UnOp _ _) =
  BytesType 4
typeInf (Num n b) =
  BytesType b
typeInf (Pi _ _ _) =
  Type
typeInf (Call v ts ty) =
  ty

flattenPi :: Type -> ([Type], Type)
flattenPi (Pi _ ty1 ty2) =
  let (args, ret) = flattenPi ty2
  in (ty1 : args, ret)
flattenPi t =
  ([], t)
