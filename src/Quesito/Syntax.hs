module Quesito.Syntax
  ( Term(..)
  , Def(..)
  , getNames
  , convertDef
  )
  where

import Quesito
import qualified Quesito.TT as TT
import Quesito.TT (Flags)

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

convert :: [String] -> Term -> Ques TT.Term
convert env (Var v)
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
convert _ (Num n) =
  return (TT.Num n)
convert _ (App (Var "Bytes") [Num n]) =
  return (TT.BytesType n)
convert _ (App (Var "Bytes") _) = do
  loc <- getLocation
  throwError ("Type error on Bytes at " ++ pprint loc)
convert _ (App (Var "Type") [Num n]) =
  return (TT.Type n)
convert _ (App (Var "Type") _) = do
  loc <- getLocation
  throwError ("Type error on Type at " ++ pprint loc)
convert env (App t args) =
  foldl TT.App <$> convert env t <*> mapM (convert env) args
convert env (Lam v body) =
  TT.Lam v <$> convert env body
convert env (Arrow (Ann (Var v) ty1) ty2) =
  TT.Pi v <$> convert env ty1 <*> convert env ty2
convert _ (Arrow (Ann _ _) _) = do
  loc <- getLocation
  throwError ("Type annotation not allowed here " ++ pprint loc)
convert env (Arrow ty1 ty2) =
  TT.Pi "" <$> convert env ty1 <*> convert env ty2
convert env (Ann t ty) =
  TT.Ann <$> convert env t <*> convert env ty
convert env (Loc loc t) =
  TT.Loc loc <$> convert env t `locatedAt` loc

convertDef :: [String] -> Def -> Ques TT.Def
convertDef env (PatternMatchingDef name equations ty flags) = do
  equations' <- equationsM'
  ty' <- convert (name:env) ty
  return (TT.PatternMatchingDef name (undefined equations') ty' flags)
  where
    equationsM' = flip mapM equations $ \(lhs, rhs) -> do
      lhs' <- convert (name:env) lhs
      rhs' <- convert (name:env) rhs
      return (lhs', rhs')
convertDef env (TypeDef name ty constructors) = do
  ty' <- convert env ty
  constructors' <- flip mapM constructors (\(name', t) -> do
      t' <- convert (name:env) t
      return (name', t')
    )
  return (TT.TypeDef name ty' constructors')
