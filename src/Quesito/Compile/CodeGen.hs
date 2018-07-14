module Quesito.Compile.CodeGen where

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

compilePushEnv :: String -> String -> String
compilePushEnv fName var =
  fName ++ ".env[" ++ fName ++ ".envn++] = " ++ var ++ ";\n"

compileCallFunc :: String -> String -> Ty -> String
compileCallFunc retName fName ty =
  cType ty ++ " (* " ++ fName ++ "_)(struct fn) = " ++ fName ++ ".f;\n"
  ++ cType ty ++ " " ++ retName ++ " = (*" ++ fName ++ "_)(" ++ fName ++ ");\n"

compile :: AnnTerm -> NameProv Compilation
compile t'@(AnnLambda v t (Arrow ty ty')) = do
  retName <- newName
  name' <- newName
  Compilation tCode tName tExtraDecl <- compile t
  return $ Compilation
    { code =
        "struct fn " ++ retName ++ ";\n"
        ++ retName ++ ".f = &" ++ name' ++ ";\n"
        ++ retName ++ ".n = 0;\n"
        ++ retName ++ ".envn = 0;\n"
        ++ (concat $
              map
                (\(v_, _) ->
                   compilePushEnv retName (v_ : [])
                )
                (freeVars t')
           )
    , name = retName
    , extraDecl =
        tExtraDecl ++
        [ cType ty' ++ " " ++ name' ++ "(struct fn f)\n"
          ++ "{\n"
          ++ cType ty ++ " " ++ v : [] ++ " = f.args[0];\n"
          ++ (concat $
                map
                  (\(n, (v_, _)) ->
                     cType ty ++ " " ++ v_ : [] ++ " = f.env[" ++ show (n :: Int) ++ "];\n"
                  )
                  (zip [0..] $ freeVars t')
             )
          ++ tCode
          ++ "return " ++ tName ++ ";\n"
          ++ "}\n"
        ]
    }
compile (AnnLambda _ _ _) = undefined
compile (AnnApp t t' ty) = do
  retName <- newName
  Compilation code_ name_ extraDecl_ <- compile t
  Compilation code' name' extraDecl' <- compile t'
  return $ Compilation
    { code =
        code_
        ++ code'
        ++ compilePushArg name_ name'
        ++ compileCallFunc retName name_ ty
    , name = retName
    , extraDecl = extraDecl_ ++ extraDecl'
    }
compile (AnnConstant Plus2 _) = return $ Compilation
  { code =
      "struct fn plus2_;\n"
      ++ "plus2_.f = &plus2;\n"
      ++ "plus2_.n = 0;\n"
  , name = "plus2_"
  , extraDecl = []
  }
compile (AnnVar v _) = return $ Compilation "" (v : []) []
compile (AnnConstant (Num n) _) = return $ Compilation "" (show n) []
compile (AnnConstant (Plus1 _) _) = undefined

stdLib :: [String]
stdLib =
  [    "struct fn {" ++ "\n"
    ++ "    void *f;" ++ "\n"
    ++ "    int args[8];" ++ "\n"
    ++ "    int n;" ++ "\n"
    ++ "    int env[24];" ++ "\n"
    ++ "    int envn;" ++ "\n"
    ++ "};" ++ "\n"
  ,    "int plus1(struct fn f) {" ++ "\n"
    ++ "    return f.args[0] + f.env[0];" ++ "\n"
    ++ "}" ++ "\n"
  ,    "struct fn plus2(struct fn f) {" ++ "\n"
    ++ "    struct fn fn;" ++ "\n"
    ++ "    fn.f = &plus1;" ++ "\n"
    ++ "    fn.n = 0;" ++ "\n"
    ++ "    fn.env[0] = f.args[0];" ++ "\n"
    ++ "    fn.envn = 1;" ++ "\n"
    ++ "    return fn;" ++ "\n"
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
