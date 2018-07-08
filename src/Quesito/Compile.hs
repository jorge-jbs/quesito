module Quesito.Compile where

import Quesito.AnnTerm
import Quesito.Constant
import Quesito.Type

cType :: Ty -> String
cType (BaseTy Nat) = "unsigned int"
cType (Arrow _ _) = "struct fn"

data Compilation = Compilation
  { code :: String
  , name :: String
  , extraDecl :: [String]
  }
  deriving Show

compilePushArg :: String -> String -> String
compilePushArg fName arg =
  fName ++ ".args[" ++ fName ++ ".n++] = " ++ arg ++ ";\n"

compileCallFunc :: String -> String -> Ty -> String
compileCallFunc retName fName ty =
  cType ty ++ " (* " ++ fName ++ "_)(struct fn) = " ++ fName ++ ".f;\n"
  ++ cType ty ++ " " ++ retName ++ " = (*" ++ fName ++ "_)(" ++ fName ++ ");\n"

compile :: AnnTerm -> Compilation
compile (AnnLambda v t (Arrow ty ty')) = Compilation
  { code =
      "struct fn hue;\n"
      ++ "fn.f = &hue;\n"
      ++ "fn.n = 0;\n"
  , name = "hue"
  , extraDecl =
      tExtraDecl ++
      [ cType ty' ++ " hue(struct fn f)\n"
        ++ "{\n"
        ++ cType ty ++ " " ++ v : [] ++ " = f.args[0];\n"
        ++ tCode
        ++ "return " ++ tName ++ ";\n"
        ++ "}\n"
      ]
  }
  where
    Compilation tCode tName tExtraDecl = compile t
compile (AnnLambda _ _ _) = undefined
compile (AnnApp t t' ty) = Compilation
  { code =
      code_
      ++ code'
      ++ compilePushArg name_ name'
      ++ case ty of
           BaseTy _ -> compileCallFunc "hue" name_ ty
           Arrow _ _ -> ""
  , name = "hue"
  , extraDecl = extraDecl_ ++ extraDecl'
  }
  where
    Compilation code_ name_ extraDecl_ = compile t
    Compilation code' name' extraDecl' = compile t'
compile (AnnConstant Plus2 _) = Compilation
  { code =
      "struct fn add;\n"
      ++ "fn.f = &add;\n"
      ++ "fn.n = 0;\n"
  , name = "plus2"
  , extraDecl = []
  }
compile (AnnVar v _) = Compilation "" (v : []) []
compile (AnnConstant (Num n) _) = Compilation "" (show n) []
compile (AnnConstant (Plus1 _) _) = undefined

stdLib :: [String]
stdLib =
  [    "int add(struct fn f) {" ++ "\n"
    ++ "    return f.args[0] + f.args[1];" ++ "\n"
    ++ "}" ++ "\n"
  ]

toProgram :: Compilation -> String
toProgram (Compilation code' name' extraDecl') =
  concat (stdLib ++ extraDecl')
  ++ "int main()\n"
  ++ "{\n"
  ++ code'
  ++ "printf(\"%d\", " ++ name' ++ ");\n"
  ++ "}\n"
