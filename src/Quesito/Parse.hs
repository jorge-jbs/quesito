module Quesito.Parse
  ( parse
  , ParseError
  , ParserResult
  , Pos
  ) where

import Control.Monad.State (State, evalState, modify, get)

import Quesito.Constant as C
import Quesito.Expr
import Quesito.Type

data ParseError
  = MismatchedParenthesis
  | ReachedEndOfFile
  | MalformedType
  | MultipleArguments
  deriving Show

type ParserResult a = Either (ParseError, Pos) a

data Pos = Pos Int Int
  deriving (Show, Eq)

data SExpr
  = Symbol String Pos
  | Num Int Pos
  | List [SExpr] Pos
  deriving (Show, Eq)

data Token
  = ParenBegin Pos
  | ParenEnd Pos
  | SymbolT String Pos
  deriving (Show)

astPos :: SExpr -> Pos
astPos (Symbol _ pos) = pos
astPos (Quesito.Parse.Num _ pos) = pos
astPos (List _ pos) = pos

tokenPos :: Token -> Pos
tokenPos (ParenBegin pos) = pos
tokenPos (ParenEnd pos) = pos
tokenPos (SymbolT _ pos) = pos

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace ',' = True
isWhitespace '\n' = True
isWhitespace _ = False

isDelimiter :: Char -> Bool
isDelimiter '(' = True
isDelimiter ')' = True
isDelimiter c = isWhitespace c

moveRight :: Int -> Pos -> Pos
moveRight n (Pos column row) = Pos (column + n) row

moveDown :: Pos -> Pos
moveDown (Pos _ row) = Pos 0 (row + 1)

tokenize :: String -> State Pos [Token]
tokenize [] = return []
tokenize (c : str) | isWhitespace c = do
  if c == '\n' then modify moveDown else modify (moveRight 1)
  tokenize str
tokenize ('(' : str) = do
  n <- get
  modify (moveRight 1)
  ts <- tokenize str
  return (ParenBegin n : ts)
tokenize (')' : str) = do
  n <- get
  modify (moveRight 1)
  ts <- tokenize str
  return (ParenEnd n : ts)
tokenize str = do
  n <- get
  let symbolS = takeWhile (not . isDelimiter) str
  modify (moveRight (length symbolS))
  ts <- tokenize (dropWhile (not . isDelimiter) str)
  return (SymbolT symbolS n : ts)

parseList :: [Token] -> ParserResult ([SExpr], [Token])
parseList (ParenEnd _ : ts) = return ([], ts)
parseList ts = do
  (x, ts') <- parse' ts
  (xs, ts'') <- parseList ts'
  return (x : xs, ts'')

parse' :: [Token] -> ParserResult (SExpr, [Token])
parse' (SymbolT sym pos : ts) = return (ast, ts)
  where
    ast :: SExpr
    ast =
      if all (\c -> elem c "0123456789") sym then
        Quesito.Parse.Num (read sym) pos
      else
        Symbol sym pos
parse' (ParenBegin pos : ts) = do
  (xs, ts') <- parseList ts
  return (List xs pos, ts')
parse' [] = Left (ReachedEndOfFile, Pos 0 0)
parse' (ParenEnd pos : _) = Left (MismatchedParenthesis, pos)

parseToSExpr :: String -> ParserResult SExpr
parseToSExpr s = fst <$> (parse' . flip evalState (Pos 0 0) $ tokenize s)

parse :: String -> ParserResult QuesExpr
parse s = sexpQuesExpr =<< parseToSExpr s

parseType :: SExpr -> ParserResult Type
parseType (Symbol "Nat" _) = return (BaseType Nat)
parseType (List (Symbol "->" pos : tys) _)
  | length tys < 2 = Left (MalformedType, pos)
  | otherwise = return . typesToArrow =<< sequence (map parseType tys)
  where
    typesToArrow :: [Type] -> Type
    typesToArrow (t:t':[]) = Arrow t t'
    typesToArrow (t:ts) = Arrow t (typesToArrow ts)
    typesToArrow [] = undefined
parseType ast = Left (MalformedType, astPos ast)

sexpQuesExpr :: SExpr -> ParserResult QuesExpr
sexpQuesExpr (Symbol "+" _) = return (Constant Plus2)
sexpQuesExpr (Symbol s _) = return (Var s)
sexpQuesExpr (Quesito.Parse.Num x _) = return (Constant (C.Num x))
sexpQuesExpr (List [Symbol "lambda" _, List [Symbol s _, tyS] _, tS] _) = do
  ty <- parseType tyS
  t <- sexpQuesExpr tS
  return (Lambda s ty t)
sexpQuesExpr (List [Symbol "let" _, List [Symbol v _, t] _, t'] _) = do
  t'' <- sexpQuesExpr t
  t''' <- sexpQuesExpr t'
  return (Let (v, t'') t''')
sexpQuesExpr (List [t, t'] _) = do
  t'' <- sexpQuesExpr t
  t''' <- sexpQuesExpr t'
  return (App t'' t''')
sexpQuesExpr (List _ pos) = Left (MultipleArguments, pos)
