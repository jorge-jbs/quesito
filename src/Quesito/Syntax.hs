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
  deriving Show

getNames :: Def -> [String]
getNames (PatternMatchingDef name _ _ _) =
  [name]
getNames (TypeDef name _ conss) =
  name : map fst conss

desugar :: [String] -> Term -> Ques TT.Term
desugar env (Var v)
  | v `elem` env =
      return (TT.Global v)
  | otherwise =
      case v of
      "Bytes" -> do
        loc <- getLocation
        throwError ("Type error on Bytes at " ++ pprint loc)
      "Type" ->
        return (TT.Type 0)
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
  loc <- getLocation
  throwError ("Type error on Bytes at " ++ pprint loc)
desugar _ (App (Var "Type") [Num n]) =
  return (TT.Type n)
desugar _ (App (Var "Type") _) = do
  loc <- getLocation
  throwError ("Type error on Type at " ++ pprint loc)
desugar env (App t args) =
  foldl TT.App <$> desugar env t <*> mapM (desugar env) args
desugar env (Lam v body) =
  TT.Lam v <$> desugar env body
desugar env (Arrow (Ann (Var v) ty1) ty2) =
  TT.Pi v <$> desugar env ty1 <*> desugar env ty2
desugar _ (Arrow (Ann _ _) _) = do
  loc <- getLocation
  throwError ("Type annotation not allowed here " ++ pprint loc)
desugar env (Arrow ty1 ty2) =
  TT.Pi "" <$> desugar env ty1 <*> desugar env ty2
desugar env (Ann t ty) =
  TT.Ann <$> desugar env t <*> desugar env ty
desugar env (Loc loc t) =
  TT.Loc loc <$> desugar env t `locatedAt` loc

desugarDef :: Env.Env TT.Def -> Def -> Ques TT.Def
desugarDef env (PatternMatchingDef name equations ty flags) = do
  ty' <- desugar (name : Env.keys env) ty
  equations' <- forM equations $ \(lhs, rhs) -> do
      lhs' <- desugar (name : Env.keys env) lhs
      rhs' <- desugar (name : Env.keys env) rhs
      return (lhs', rhs')
  return (TT.PatternMatchingDef name equations' ty' flags)
desugarDef env (TypeDef name ty constructors) = do
  ty' <- desugar (Env.keys env) ty
  constructors' <- flip mapM constructors (\(name', t) -> do
      t' <- desugar (name : Env.keys env) t
      return (name', t')
    )
  return (TT.TypeDef name ty' constructors')
