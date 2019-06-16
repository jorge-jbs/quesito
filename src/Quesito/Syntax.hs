module Quesito.Syntax
  ( Term(..)
  , Def(..)
  , getNames
  , desugarDef
  )
  where

import Control.Monad (forM)

import Quesito
import qualified Quesito.TT as TT
import Quesito.TT (Flags)
import qualified Quesito.Env as Env

data Term
  = Var String
  | Num Int
  | Arrow Term Term
  | UniqueArrow Term Term
  | SharedArrow Term Term
  | App Term [Term]
  | Lam String Term
  | Ann Term Term
  | Loc Location Term
  deriving Show

data Def
  = PatternMatchingDef
      String  -- ^ name
      [(Term, Term)] -- ^ equations
      Term -- ^ type
      Flags
  | TypeDef
      String  -- ^ name
      Term  -- ^ type
      [(String, Term)]  -- ^ constructors
  | ExternDef String Term Flags
  deriving Show

remLoc :: Term -> Term
remLoc (Arrow r s) =
  Arrow (remLoc r) (remLoc s)
remLoc (App hd tl) =
  App (remLoc hd) (map remLoc tl)
remLoc (Ann r s) =
  Ann (remLoc r) (remLoc s)
remLoc (Loc _ t) =
  remLoc t
remLoc t =
  t

getNames :: Def -> [String]
getNames (PatternMatchingDef name _ _ _) =
  [name]
getNames (TypeDef name _ conss) =
  name : map fst conss
getNames (ExternDef name _ _) =
  [name]

desugar :: [String] -> Term -> Ques TT.Term
desugar env (Var v)
  | v `elem` env =
      return (TT.Global v)
  | otherwise =
      case v of
      "_" -> do
        return TT.Hole
      "Bytes" -> do
        loc <- askLoc
        throwError ("Type error on Bytes at " ++ pprint loc)
      "BaseType" ->
        return $ TT.BaseType 0
      "UniquenessAttr" ->
        return TT.UniquenessAttr
      "Type" ->
        return $ TT.Type 0 $ TT.AttrLit TT.SharedAttr
      "SharedAttr" ->
        return (TT.AttrLit TT.SharedAttr)
      "UniqueAttr" ->
        return (TT.AttrLit TT.UniqueAttr)
      "add"  -> return (TT.BinOp TT.Add)
      "sub"  -> return (TT.BinOp TT.Sub)
      "mul"  -> return (TT.BinOp TT.Mul)
      "udiv" -> return (TT.BinOp TT.UDiv)
      "sdiv" -> return (TT.BinOp TT.SDiv)
      "and"  -> return (TT.BinOp TT.And)
      "or"   -> return (TT.BinOp TT.Or)
      "xor"  -> return (TT.BinOp TT.Xor)
      "shr"  -> return (TT.BinOp TT.Shr)
      "shl"  -> return (TT.BinOp TT.Shl)
      "not"  -> return (TT.UnOp TT.Not)
      _ ->
        return (TT.Local v)
desugar _ (Num n) =
  return (TT.Num n)
desugar _ (App (Var "Bytes") [Num n]) =
  return (TT.BytesType n)
desugar _ (App (Var "Bytes") _) = do
  loc <- askLoc
  throwError ("Type error on Bytes at " ++ pprint loc)
desugar env (App (Var "Type") [Num n, u]) =
  TT.Type n <$> desugar env u
desugar _ (App (Var "BaseType") [Num n]) =
  return $ TT.BaseType n
desugar env (App (Var "Attr") [ty, u]) =
  TT.Attr <$> desugar env ty <*> desugar env u
desugar _ (App (Var "Type") _) = do
  loc <- askLoc
  throwError ("Type error on Type at " ++ pprint loc)
desugar env (App t args) =
  foldl TT.App <$> desugar env t <*> mapM (desugar env) args
desugar env (Lam v body) =
  TT.Lam v <$> desugar env body
desugar env (Arrow ty1 ty2) =
  case remLoc ty1 of
    Ann (Var v) ty1' ->
      TT.Pi v <$> desugar env ty1' <*> desugar env ty2
    Ann _ _ -> do
      loc <- askLoc
      throwError ("Type annotation not allowed here " ++ pprint loc ++ ": " ++ show ty1)
    _ ->
      TT.Pi "" <$> desugar env ty1 <*> desugar env ty2
desugar env (UniqueArrow ty1 ty2) = do
  ty <- desugar env $ Arrow ty1 ty2
  return $ TT.Attr ty $ TT.AttrLit TT.UniqueAttr
desugar env (SharedArrow ty1 ty2) = do
  ty <- desugar env $ Arrow ty1 ty2
  return $ TT.Attr ty $ TT.AttrLit TT.SharedAttr
desugar env (Ann t ty) =
  TT.Ann <$> desugar env t <*> desugar env ty
desugar env (Loc loc t) =
  TT.Loc loc <$> desugar env t `withLoc` loc

desugarDef :: Env.Env TT.Def -> Def -> Ques TT.Def
desugarDef env (PatternMatchingDef name equations ty flags) = do
  ty' <- desugar (name : Env.keys env) ty
  equations' <- forM equations $ \(lhs, rhs) -> do
      lhs' <- desugar (name : Env.keys env) lhs
      rhs' <- desugar (name : Env.keys env) rhs
      return (lhs', rhs')
  return (TT.PatternMatchingDef name equations' ty' flags)
desugarDef env (ExternDef name ty flags) = do
  ty' <- desugar (name : Env.keys env) ty
  return (TT.ExternDef name ty' flags)
desugarDef env (TypeDef name ty constructors) = do
  ty' <- desugar (Env.keys env) ty
  constructors' <- flip mapM constructors (\(name', t) -> do
      t' <- desugar (name : Env.keys env) t
      return (name', t')
    )
  return (TT.TypeDef name ty' constructors')
