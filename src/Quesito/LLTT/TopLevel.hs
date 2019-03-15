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
      t' <- lower env t
      return (vars', pats, t')
    )
  ty' <- lower env ty
  return [PatternMatchingDef name equations' ty']
lowerDef env (Ann.TypeDef name ty conss) = do
  ty' <- lower env ty
  conss' <- mapM
      (\(consName, consTy) ->
        ConstructorDef consName <$> lower env consTy
      )
      conss
  equations <- forM conss (\(_, consTy) -> do
      let (args, retTy) = Ann.flattenPi consTy
          termToPattern' = TT.termToPattern (\x -> case Env.lookup x env of
              Just (ConstructorDef _ _) ->
                True
              _ ->
                False
            )
      args' <- mapM (lower env) args
      pats <- mapM termToPattern' $ tail $ Ann.flattenApp retTy
      vars <- mapM
          (\(v, vty) -> do vty' <- lower env vty; return (v, vty'))
          $ TT.findVars retTy
      return (vars, pats, args')
    )
  return (TypeDef name equations ty' : conss')
