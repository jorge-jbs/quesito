module Quesito.LLTT where

import Quesito
import Quesito.TT (BinOp(..), UnOp(..))
import Quesito.Ann (Pattern)
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
      Int -- ^ literal
      Int -- ^ bytes
  | Pi String Type Type
  | Type Int
  | BytesType Int
  | Call Var [Term]
  | BinOp BinOp Term Term
  | UnOp UnOp Term
  deriving Show

type Type = Term

type Env = Env.Env Def

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
    Just (TypeDef n _ _) ->
      Constant . TypeCons v <$> lower env ty
    Just (ConstructorDef _ _ _) ->
      Constant . Constructor v <$> lower env ty
    Just (PatternMatchingDef _ _ _) ->
      Constant . Global v <$> lower env ty
    _ ->
      error ""
lower _ (Ann.Type i) =
  return $ Type i
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
      case hd' of
        Constant v ->
          Call v <$> mapM (lower env) tl
        _ ->
          error ""
    [] ->
      error ""
lower _ (Ann.Lam _ _ _) =
  throwError "Can't generate lambda expressions"

flattenPi = undefined
