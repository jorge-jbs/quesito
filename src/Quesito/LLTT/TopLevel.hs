{-# LANGUAGE FlexibleContexts #-}
module Quesito.LLTT.TopLevel where

import Control.Monad (forM)

import Quesito
import Quesito.LLTT
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env
import qualified Quesito.TT.TopLevel as TT

lowerDef :: (MonadExcept m, MonadLocatable m, MonadLog m) => Env -> Ann.Def -> m [Def]
lowerDef env (Ann.PatternMatchingDef name equations ty _) = do
  equations' <- forM equations (\(vars, pats, t) -> do
      vars' <- mapM (\(v, vty) -> do vty' <- lower vty `withEnv` env; return (v, vty')) vars
      pats' <- mapM lowerPat pats `withEnv` env
      t' <- lower t `withEnv` env
      return (vars', pats', t')
    )
  ty' <- lower ty `withEnv` env
  return [PatternMatchingDef name equations' ty']
lowerDef env (Ann.TypeDef name ty conss) = do
  tell name
  ty' <- lower ty `withEnv` env
  equations <- forM conss (\(_, consTy) -> do
      let (args, retTy) = Ann.flattenPi consTy
          termToPattern' = TT.termToPattern (\x -> case Env.lookup x env of
              Just (ConstructorDef _ _ _) ->
                True
              _ ->
                False
            )
      args' <- mapM lower args `withEnv` Env.insert (TypeDef name undefined undefined) env
      pats <- mapM
          (\t -> do pat <- termToPattern' t; lowerPat pat `withEnv` env)
          $ tail $ Ann.flattenApp retTy
      vars <- mapM
          (\(v, vty) -> do vty' <- lower vty `withEnv` env; return (v, vty'))
          $ TT.findVars retTy
      return (vars, pats, args')
    )
  let env' = Env.insert (TypeDef name equations ty') env
  conss' <- mapM
      (\((consName, consTy), tag) ->
        ConstructorDef consName <$> lower consTy `withEnv` env' <*> pure tag
      )
      (zip conss [0..])
  return (TypeDef name equations ty' : conss')
