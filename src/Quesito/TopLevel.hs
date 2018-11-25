module Quesito.TopLevel where

import Quesito
import Quesito.Ann as Ann
import Quesito.LC as LC
import Quesito.TT as TT
import Quesito.TT.TopLevel

declToLcDecl
  :: [(Ann.Name, Ann.Term Ann.Name)]
  -> Decl
  -> Ques
       ( LC.Name
       , [(LC.Name, LC.Type LC.Name)]
       , LC.Term LC.Name
       , LC.Type LC.Name
       , Ann.Term Ann.Name
       )
-- declToLcDecl (MatchFunctionDecl _ _ _) = undefined
declToLcDecl env (ExprDecl name expr ty) = do
  ty' <- annotate env [] ty
  annExpr <- annotate' env [] expr ty
  (args, body, retTy) <- flatten annExpr ty' []
  return (name, args, body, retTy, ty')
  where
    flatten
      :: Ann.Term Ann.Name
      -> Ann.Term Ann.Name
      -> [(Ann.Name, Ann.Term Ann.Name)]
      -> Ques ([(LC.Name, LC.Type LC.Name)], LC.Term LC.Name, LC.Type LC.Name)
    flatten (Ann.Loc loc t) ty' ctx =
      flatten t ty' ctx `locatedAt` loc
    flatten (Ann.Lam argName ty1 t ty2) _ ctx = do
      ty1' <- cnvType ty1
      (args, body, retTy) <- flatten t ty2 ((argName, ty1) : ctx)
      return ((argName, ty1') : args, body, retTy)
    flatten body retTy _ = do
      body' <- cnvBody body
      retTy' <- cnvType retTy
      return ([], body', retTy')
