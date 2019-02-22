module Quesito.Syntax
  ( Term(..)
  , Def(..)
  , getNames
  , convertDef
  )
  where

import Data.Default

import Quesito
import qualified Quesito.TT as TT hiding (Env)
import qualified Quesito.TT.TypeAnn as TT
import qualified Quesito.Ann as Ann
import qualified Quesito.Ann.Eval as Ann
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

convertDef :: TT.Env -> Def -> Ques TT.Def
convertDef = undefined
{-
convertDef env (PatternMatchingDef name equations ty flags) = do
  tell ("Checking pattern matching function definition " ++ name ++ " " ++ show (TT.annEnvKeys env))
  ty' <- convert (name : TT.annEnvKeys env) ty
  (_, annTy) <- TT.typeInfAnn env [] ty'
  -- TODO check type
  equations' <- flip mapM equations $ \(lhs, rhs) -> do
      lhs' <- convert (name : TT.annEnvKeys env) lhs
      rhs' <- convert (name : TT.annEnvKeys env) rhs
      pats <- mapM (termToPattern env) (tail $ TT.flattenApp lhs')
      let env' = TT.annEnvInsert (TT.PatternMatchingDef name [] ty' (TT.Flags False)) annTy env
      (lhsTy, annLhs) <- TT.typeInfAnn' (def { TT.inferVars = True }) env' [] lhs'
      vars <- findVars annLhs
      _ <- TT.typeCheckAnn env' vars rhs' lhsTy
      return (pats, rhs')
  return (TT.PatternMatchingDef name equations' ty' flags, annTy)
  where
    findVars :: MonadQues m => Ann.Term -> m [(String, TT.Value, Ann.Term)]
    findVars (Ann.Local v varTy) = do
      varTy' <- TT.eval (TT.dropAnn env) [] (Ann.downgrade varTy)
      return [(v, varTy', varTy)]
    findVars (Ann.App s _ t _) =
      (++) <$> findVars s <*> findVars t
    findVars _ =
      return []
convertDef env (TypeDef name ty constructors) = do
  tell ("Checking type definition " ++ name ++ " " ++ show (TT.annEnvKeys env))
  ty' <- convert (TT.annEnvKeys env) ty
  (_, annTy) <- TT.typeInfAnn env [] ty'
  -- TODO check type
  constructors' <- flip mapM constructors (\(name', t) -> do
      t' <- convert (name : TT.annEnvKeys env) t
      _ <- TT.typeInfAnn (TT.annEnvInsert (TT.TypeDef name ty' []) annTy env) [] t'
      return (name', t')
    )
  return (TT.TypeDef name ty' constructors', annTy)

termToPattern :: MonadQues m => TT.Env -> TT.Term -> m TT.Pattern
termToPattern _ (TT.Local x) =
  return (TT.Binding x)
termToPattern env (TT.Global x) =
  case TT.lookupAnnEnv x env of
    Just (TT.TypeDef _ _ conss, _) | x `elem` map fst conss ->
      return (TT.Constructor x)
    _ -> do
      loc <- getLocation
      throwError ("Free variable at " ++ pprint loc ++ ".")
termToPattern env (TT.App l r) = do
  l' <- termToPattern env l
  r' <- termToPattern env r
  return (TT.PatApp l' r')
termToPattern _ (TT.Num x) =
  return (TT.NumPat x)
termToPattern _ (TT.BinOp _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
termToPattern _ (TT.UnOp _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type built-in operations (at " ++ pprint loc ++ ")")
termToPattern _ (TT.Type _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type universes (at " ++ pprint loc ++ ")")
termToPattern _ (TT.BytesType _) = do
  loc <- getLocation
  throwError ("Can't pattern match on bytes types (at " ++ pprint loc ++ ")")
termToPattern _ (TT.Pi _ _ _) = do
  loc <- getLocation
  throwError ("Can't pattern match on function spaces (at " ++ pprint loc ++ ")")
termToPattern _ (TT.Ann _ _) = do
  loc <- getLocation
  throwError ("Can't pattern match on type annotations (at " ++ pprint loc ++ ")")
termToPattern _ (TT.Lam _ _) = do
  loc <- getLocation
  throwError ("Can't pattern match on lambda expressions (at " ++ pprint loc ++ ")")
termToPattern env (TT.Loc loc t) =
  termToPattern env t `locatedAt` loc
-}
