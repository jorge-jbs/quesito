module Quesito.Ann.TopLevel where

import Control.Monad (forM)

import Quesito
import Quesito.Ann
import qualified Quesito.LC as LC
import qualified Quesito.LC.TopLevel as LC

convert :: MonadQues m => Def -> m LC.Def
convert (PatternMatchingDef name equations ty flags) = do
  let (argsTy, retTy) = flattenPi ty
  argsTy' <- mapM LC.cnvType argsTy
  retTy' <- LC.cnvType retTy
  equations' <- forM equations (\(vars, pats, rhs) -> do
      vars' <- mapM (\(x, vty) -> (,) x <$> LC.cnvType vty) vars
      let pats' = map convertPattern pats
      rhs' <- LC.cnvBody rhs
      return (vars', pats', rhs')
    )
  return (LC.PatternMatchingDef name equations' argsTy' retTy' flags)
  where
    convertPattern :: Pattern -> LC.Pattern
    convertPattern (Binding x) =
      LC.Binding x
    convertPattern (Inaccessible _) =
      undefined
    convertPattern (NumPat n b) =
      LC.NumPat n b
    convertPattern (Constructor x) =
      LC.Constructor x []
    convertPattern (PatApp p q) =
      case convertPattern p of
        LC.Constructor x args ->
          LC.Constructor x (args ++ [convertPattern q])
        _ ->
          undefined
convert (TypeDef name _ conss) = do
  conss' <- mapM (\(v, ty) -> (,) v <$> LC.cnvType ty) conss
  return (LC.TypeDef name conss')
