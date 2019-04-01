module Quesito.LLTT.TopLevel where

import Control.Monad (forM)

import Quesito
import Quesito.LLTT
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env
import qualified Quesito.TT.TopLevel as TT

lowerDef :: MonadQues m => Env -> Ann.Def -> m [Def]
lowerDef env (Ann.PatternMatchingDef name equations ty _) = do
  equations' <- forM equations (\(vars, pats, t) -> do
      vars' <- mapM (\(v, vty) -> do vty' <- lower env vty; return (v, vty')) vars
      pats' <- mapM (lowerPat env) pats
      t' <- lower env t
      return (vars', pats', t')
    )
  ty' <- lower env ty
  return [PatternMatchingDef name equations' ty']
lowerDef env (Ann.TypeDef name ty conss) = do
  tell name
  ty' <- lower env ty
  equations <- forM conss (\(_, consTy) -> do
      let (args, retTy) = Ann.flattenPi consTy
          termToPattern' = TT.termToPattern (\x -> case Env.lookup x env of
              Just (ConstructorDef _ _ _) ->
                True
              _ ->
                False
            )
      args' <- mapM (lower $ Env.insert (TypeDef name undefined undefined) env) args
      pats <- mapM (\t -> do pat <- termToPattern' t; lowerPat env pat) $ tail $ Ann.flattenApp retTy
      vars <- mapM
          (\(v, vty) -> do vty' <- lower env vty; return (v, vty'))
          $ TT.findVars retTy
      return (vars, pats, args')
    )
  let env' = Env.insert (TypeDef name equations ty') env
  conss' <- mapM
      (\((consName, consTy), tag) ->
        ConstructorDef consName <$> lower env' consTy <*> pure tag
      )
      (zip conss [0..])
  return (TypeDef name equations ty' : conss')
