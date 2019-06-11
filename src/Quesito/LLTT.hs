{-# LANGUAGE FlexibleContexts #-}

module Quesito.LLTT where

import Quesito
import Quesito.TT (BinOp(..), UnOp(..))
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env
import Quesito.Ann.Eval (Value(..), Normal(..))

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

lowerPat :: (MonadEnv Def m, MonadExcept m) => Ann.Pattern -> m Pattern
lowerPat (Ann.Binding v ty) =
  Ann.Binding v <$> lower ty
lowerPat (Ann.Inaccessible t) =
  Ann.Inaccessible <$> lower t
lowerPat (Ann.NumPat n b) =
  return $ Ann.NumPat n b
lowerPat (Ann.NumSucc p) =
  Ann.NumSucc <$> lowerPat p
lowerPat (Ann.Constructor v) =
  return $ Ann.Constructor v
lowerPat (Ann.PatApp r s) =
  Ann.PatApp <$> lowerPat r <*> lowerPat s

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

lower :: (MonadEnv Def m, MonadExcept m) => Ann.Term -> m Term
lower (Ann.Local v ty _) =
  Constant . Local v <$> lower ty
lower (Ann.Global v ty) = do
  env <- askEnv
  case Env.lookup v env of
    Just (TypeDef _ _ _) ->
      Constant . TypeCons v <$> lower ty
    Just (ConstructorDef _ _ _) ->
      Constant . Constructor v <$> lower ty
    _ ->
      Constant . Global v <$> lower ty
lower (Ann.Type i _) =
  return Type
lower (Ann.BytesType i) =
  return $ BytesType i
lower (Ann.BinOp op) =
  error ""
lower (Ann.UnOp op) =
  error ""
lower (Ann.Num n i) =
  return $ Num n i
lower (Ann.Pi v ty1 ty2) =
  Pi v <$> lower ty1 <*> lower ty2
lower t@(Ann.App _ _) =
  case Ann.flattenApp t of
    [Ann.BinOp op, a, b] ->
      BinOp op <$> lower a <*> lower b
    [Ann.UnOp op, a] ->
      UnOp op <$> lower a
    hd : tl -> do
      hd' <- lower hd
      tl' <- mapM lower tl
      ty <- lower $ snd $ Ann.flattenPi $ Ann.typeInf t
      case hd' of
        Constant v ->
          return $ Call v tl' ty
        _ ->
          error ""
    [] ->
      error ""
lower (Ann.Lam _ _ _) =
  throwError "Can't generate lambda expressions"

typeInf :: Term -> Type
typeInf (Constant (Local _ ty)) =
  ty
typeInf (Constant (TypeCons _ ty)) =
  ty
typeInf (Constant (Constructor _ ty)) =
  ty
typeInf (Constant (Global _ ty)) =
  ty
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
