module Quesito.TopLevel where

import Quesito
import Quesito.Ann as Ann
import Quesito.LC as LC
import Quesito.TT as TT
import Quesito.TT.TopLevel

declToLcDecl
  :: Decl
  -> Ques
       ( LC.Name
       , [(LC.Name, LC.Type LC.Name)]
       , LC.Term LC.Name
       , LC.Type LC.Name
       )
-- declToLcDecl (MatchFunctionDecl _ _ _) = undefined
declToLcDecl (ExprDecl name expr ty) = do
  ty' <- annotate [] ty
  (args, body, retTy) <- flatten expr ty' []
  return (name, args, body, retTy)
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
      body' <- cnvBody =<< annotate ctx body
      retTy' <- cnvType retTy
      return ([], body', retTy')
