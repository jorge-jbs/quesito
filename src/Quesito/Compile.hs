module Quesito.Compile where

import Data.List (intersperse)
import Data.Maybe (fromJust)

import Quesito.AnnTerm
import Quesito.Type

uncurryType :: Ty -> ([Ty], Ty)
uncurryType (Arrow ty ty') =
  let p = uncurryType ty'
  in (ty : fst p, snd p)
uncurryType ty = ([], ty)

functionParameter :: Ty -> String
functionParameter (BaseTy Nat) = "int"
functionParameter (Arrow _ _) = "void*"

functionParameters :: [Ty] -> String
functionParameters l =
  concat
  . intersperse ", "
  . map (\(ty, i) -> functionParameter ty ++ " arg" ++ show i)
  . zip l
  . flip take [0..]
  $ length l

functionDecl :: Ty -> String -> Maybe String
functionDecl ty@(Arrow _ _) name =
  let (parameters, ret) = uncurryType ty
  in Just (
    functionParameter ret
    ++ " "
    ++ name
    ++ "(" ++ functionParameters parameters ++ ")"
  )
functionDeclr _ = Nothing

{-@ uncurryLambda :: x : AnnTerm -> ([Char], AnnTerm, ([Ty], Ty)) @-}
uncurryLambda :: AnnTerm -> ([Char], AnnTerm, ([Ty], Ty))
uncurryLambda (AnnLambda v t ty) = (v : vs, t', uncurryType ty)
  where
    (vs, t', _) = uncurryLambda t
uncurryLambda t = ([], t, ([], annotatedType t))

functionBody :: AnnTerm -> Maybe String
functionBody t@(AnnLambda _ _ ty) = do
  let (_, expr, _) = uncurryLambda t
  (body, bodyName) <- compileTerm expr
  return
    ( fromJust (functionDecl ty "hue") ++ "\n"
      ++ "{" ++ "\n"
      ++ body
      ++ "return " ++ bodyName ++ ";" ++ "\n"
      ++ "}" ++ "\n"
    )

compileTerm :: AnnTerm -> Maybe (String, String)
compileTerm (AnnLambda v ty t) = Nothing
compileTerm (AnnApp t t' _) = do
  (code, name) <-  compileTerm t
  (code', name') <- compileTerm t'
  let newname = "hue"
  return
    ( code
      ++ code'
      ++ newname ++ " = " ++ name ++ "(" ++ name' ++ ");" ++ "\n"
    , newname
    )
compileTerm (AnnVar v _) = Just ("", v : [])
compileTerm (AnnConstant c _) = Just ("", show c)
