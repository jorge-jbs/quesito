module Quesito.Parse
  ( parse
  , AST(..)
  ) where

import Quesito.Term
import Quesito.Constant as C
import Quesito.Type

data AST
  = Symbol String
  | Num Int
  | List [AST]
  deriving (Show, Eq)

data Token
  = ParenBegin
  | ParenEnd
  | SymbolT String
  deriving (Show)

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace ',' = True
isWhitespace _ = False

isDelimiter :: Char -> Bool
isDelimiter '(' = True
isDelimiter ')' = True
isDelimiter c = isWhitespace c

tokenize :: String -> [Token]
tokenize [] = []
tokenize (' ' : str) = tokenize str
tokenize (',' : str) = tokenize str
tokenize ('(' : str) = ParenBegin : tokenize str
tokenize (')' : str) = ParenEnd : tokenize str
tokenize str = SymbolT (takeWhile (not . isDelimiter) str) : tokenize (dropWhile (not . isDelimiter) str)

parseList :: [Token] -> ([AST], [Token])
parseList (ParenEnd : ts) = ([], ts)
parseList ts =
  let
    (x, ts') = parse' ts
    (xs, ts'') = parseList ts'
  in
    (x : xs, ts'')

parse' :: [Token] -> (AST, [Token])
parse' (SymbolT sym : ts) = (ast, ts)
  where
    ast :: AST
    ast =
      if all (\c -> elem c "0123456789") sym then
        Quesito.Parse.Num (read sym)
      else
        Symbol sym
parse' (ParenBegin : ts) =
  let
    (xs, ts') = parseList ts
  in
    (List xs, ts')
parse' [] = undefined
parse' (ParenEnd : _) = undefined

parseToAST :: String -> AST
parseToAST = fst . parse' . tokenize

parse :: String -> Maybe Term
parse = astToTerm . parseToAST

typesToArrow :: [Ty] -> Maybe Ty
typesToArrow [] = Nothing
typesToArrow (t:t':[]) = Just (Arrow t t')
typesToArrow (_:[]) = Nothing
typesToArrow (t:ts) = Arrow t <$> typesToArrow ts

readType :: AST -> Maybe Ty
readType (Symbol "Nat") = Just (BaseTy Nat)
readType (List (Symbol "->" : tys)) = typesToArrow =<< sequence (map readType tys)
readType _ = Nothing

astToTerm :: AST -> Maybe Term
astToTerm (Symbol "+") = Just (Constant Plus2)
astToTerm (Symbol s) | length s == 1 = Just (Var (head s) Nothing)
astToTerm (Quesito.Parse.Num x) = Just (Constant (C.Num x))
astToTerm (List [Symbol "lambda", List [Symbol s, tyS], tS]) | length s == 1 = do
  ty <- readType tyS
  t <- astToTerm tS
  return (Lambda v ty t)
  where
    v = head s
astToTerm (List [t, t']) = do
  t'' <- astToTerm t
  t''' <- astToTerm t'
  return (App t'' t''')
astToTerm _ = Nothing
