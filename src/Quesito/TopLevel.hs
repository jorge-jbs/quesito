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
  (args, body, retTy) <- flatten expr ty' []
  return (name, args, body, retTy, ty')
  where
    flatten
      :: TT.Term TT.Name
      -> Ann.Term Ann.Name
      -> [(Ann.Name, Ann.Term Ann.Name)]
      -> Ques ([(LC.Name, LC.Type LC.Name)], LC.Term LC.Name, LC.Type LC.Name)
    flatten (TT.Loc loc t) ty ctx =
      flatten t ty ctx `locatedAt` loc
    flatten t (Ann.Loc loc ty) ctx =
      flatten t ty ctx `locatedAt` loc
    flatten (TT.Lam argName t) (Ann.Pi _ ty1 ty2) ctx = do
      ty1' <- cnvType ty1
      (args, body, retTy) <- flatten t ty2 ((argName, ty1) : ctx)
      return ((argName, ty1') : args, body, retTy)
    flatten body retTy ctx = do
      annBody <- annotate env ctx body
      body' <- cnvBody annBody
      retTy' <- cnvType retTy
      return ([], body', retTy')
