module Quesito.Compile where

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

compilePushArg :: String -> String -> String
compilePushArg fName arg =
  fName ++ ".args[" ++ fName ++ ".n++] = " ++ arg ++ ";\n"

compileCallFunc :: String -> String -> Ty -> String
compileCallFunc retName fName ty =
  cType ty ++ " (* " ++ fName ++ "_)(struct fn) = " ++ fName ++ ".f;\n"
  ++ cType ty ++ " " ++ retName ++ " = (*" ++ fName ++ "_)(" ++ fName ++ ");\n"

compile :: AnnTerm -> NameProv Compilation
compile (AnnLambda v t (Arrow ty ty')) = do
  name <- newName
  Compilation tCode tName tExtraDecl <- compile t
  return $ Compilation
    { code =
        "struct fn " ++ name ++ ";\n"
        ++ "fn.f = &" ++ name ++ ";\n"
        ++ "fn.n = 0;\n"
    , name = name
    , extraDecl =
        tExtraDecl ++
        [ cType ty' ++ " " ++ name ++ "(struct fn f)\n"
          ++ "{\n"
          ++ cType ty ++ " " ++ v : [] ++ " = f.args[0];\n"
          ++ tCode
          ++ "return " ++ tName ++ ";\n"
          ++ "}\n"
        ]
    }
  where
compile (AnnLambda _ _ _) = undefined
compile (AnnApp t t' ty) = do
  name <- newName
  Compilation code_ name_ extraDecl_ <- compile t
  Compilation code' name' extraDecl' <- compile t'
  return $ Compilation
    { code =
        code_
        ++ code'
        ++ compilePushArg name_ name'
        ++ -- case ty of
           --  BaseTy _ ->
              compileCallFunc name name_ ty
            -- Arrow _ _ -> ""
    , name = name
    , extraDecl = extraDecl_ ++ extraDecl'
    }
compile (AnnConstant Plus2 _) = return $ Compilation
  { code =
      "struct fn plus2;\n"
      ++ "fn.f = &add;\n"
      ++ "fn.n = 0;\n"
  , name = "plus2"
  , extraDecl = []
  }
compile (AnnVar v _) = return $ Compilation "" (v : []) []
compile (AnnConstant (Num n) _) = return $ Compilation "" (show n) []
compile (AnnConstant (Plus1 _) _) = undefined

stdLib :: [String]
stdLib =
  [    "int add(struct fn f) {" ++ "\n"
    ++ "    return f.args[0] + f.args[1];" ++ "\n"
    ++ "}" ++ "\n"
  ]

toProgram :: Compilation -> String
toProgram (Compilation code' name' extraDecl') =
  concat (map (++ "\n") (stdLib ++ extraDecl'))
  ++ "int main()\n"
  ++ "{\n"
  ++ code'
  ++ "printf(\"%d\", " ++ name' ++ ");\n"
  ++ "}\n"
