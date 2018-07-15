module Quesito.Compile.CodeGen where

import System.IO.Unsafe (unsafePerformIO)

import Quesito.AnnTerm
import Quesito.Constant
import Quesito.Type
import Quesito.NameProv

cType :: Ty -> String
cType (BaseTy Nat) = "unsigned int"
cType (Arrow _ _) = "struct fn"

data Compilation = Compilation
  { code :: String
  , name :: String
  , extraDecl :: [String]
  }
  deriving Show

compileCopy :: Char -> Ty -> String
compileCopy v ty
   = cType ty ++ " *" ++ v : "_" ++ " = malloc(sizeof(" ++ v : [] ++ "));" ++ "\n"
  ++ "*" ++ v : "_" ++ " = " ++ v : [] ++ ";" ++ "\n"

compilePushEnv :: String -> [(Char, Ty)] -> String
compilePushEnv _ [] = ""
compilePushEnv fName ((v, ty):vs)
   = "{" ++ "\n"
  ++ fName ++ ".env = newenv();" ++ "\n"
  ++ compileCopy v ty
  ++ fName ++ ".env->first = newnode(" ++ v : "_" ++ ");" ++ "\n"
  ++ "struct node *node = " ++ fName ++ ".env->first;" ++ "\n"
  ++ pushRest vs
  ++ "}" ++ "\n"
  where
    pushRest :: [(Char, Ty)] -> String
    pushRest [] = ""
    pushRest ((v', ty') : vs')
       = compileCopy v' ty'
      ++ "node = unsafepushnode(node, " ++ v' : "_" ++ ");" ++ "\n"
      ++ pushRest vs'

compilePullEnv :: [(Char, Ty)] -> String
compilePullEnv [] = ""
compilePullEnv vs
   = (concat $ map (\(v, ty) -> cType ty ++ " " ++ v : [] ++ ";\n") vs)
  ++ "{" ++ "\n"
  ++ "struct node *iter = f.env->first;" ++ "\n"
  ++ pullEnv vs
  ++ "}" ++ "\n"
  where
    pullEnv :: [(Char, Ty)] -> String
    pullEnv [] = ""
    pullEnv ((v, ty) : vs')
       = v : [] ++ " = *((" ++ cType ty ++ " *) iterget(&iter));" ++ "\n"
      ++ pullEnv vs'

compileCallFunc :: String -> String -> String -> Ty -> Ty -> String
compileCallFunc retName fName argName ty ty' =
  cType ty' ++ " (* " ++ fName ++ "_)(struct fn, " ++ cType ty ++ ") = " ++ fName ++ ".f;\n"
  ++ cType ty' ++ " " ++ retName ++ " = (*" ++ fName ++ "_)(" ++ fName ++ ", " ++ argName ++ ");\n"

compile :: AnnTerm -> NameProv Compilation
compile t'@(AnnLambda v t (Arrow ty ty')) = do
  retName <- newName
  name' <- newName
  Compilation tCode tName tExtraDecl <- compile t
  return $ Compilation
    { code =
        "struct fn " ++ retName ++ ";\n"
        ++ retName ++ ".f = &" ++ name' ++ ";\n"
        ++ compilePushEnv retName (freeVars t')
    , name = retName
    , extraDecl =
        tExtraDecl ++
        [ cType ty' ++ " " ++ name' ++ "(struct fn f, " ++ cType ty ++ " " ++ v : [] ++ ")\n"
          ++ "{\n"
          ++ compilePullEnv (freeVars t')
          ++ tCode
          ++ "return " ++ tName ++ ";\n"
          ++ "}\n"
        ]
    }
compile (AnnLambda _ _ _) = undefined
compile (AnnApp t t' _) = do
  retName <- newName
  Compilation code_ name_ extraDecl_ <- compile t
  Compilation code' name' extraDecl' <- compile t'
  return $ Compilation
    { code =
        code_
        ++ code'
        ++ compileCallFunc retName name_ name' ty ty'
    , name = retName
    , extraDecl = extraDecl_ ++ extraDecl'
    }
  where
    Arrow ty ty' = annotatedType t
compile (AnnConstant Plus2 _) = return $ Compilation
  { code =
      "struct fn plus2_;\n"
      ++ "plus2_.f = &plus2;\n"
  , name = "plus2_"
  , extraDecl = []
  }
compile (AnnVar v _) = return $ Compilation "" (v : []) []
compile (AnnConstant (Num n) _) = return $ Compilation "" (show n) []
compile (AnnConstant (Plus1 _) _) = undefined

stdLib :: String
stdLib = unsafePerformIO (readFile "std.c")

toProgram :: Compilation -> String
toProgram (Compilation code' name' extraDecl') =
  concat (map (++ "\n") (stdLib : extraDecl'))
  ++ "#include <stdio.h>\n\n"
  ++ "int main()\n"
  ++ "{\n"
  ++ code'
  ++ "printf(\"%d\", " ++ name' ++ ");\n"
  ++ "}\n"
