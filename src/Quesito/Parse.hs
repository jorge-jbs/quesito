module Quesito.Parse
  ( parse
  , AST(..)
  ) where

import Control.Monad.State (State, evalState, modify, get)

import Quesito.Term
import Quesito.Constant as C
import Quesito.Type

data ParseError
  = MismatchedParenthesis
  | ReachedEndOfFile
  | MalformedType
  | MultipleArguments
  | LengthyVar
  deriving Show

type ParserResult a = Either (ParseError, Pos) a

data Pos = Pos Int Int
  deriving (Show, Eq)

data AST
  = Symbol String Pos
  | Num Int Pos
  | List [AST] Pos
  deriving (Show, Eq)

data Token
  = ParenBegin Pos
  | ParenEnd Pos
  | SymbolT String Pos
  deriving (Show)

astPos :: AST -> Pos
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

parseList :: [Token] -> ParserResult ([AST], [Token])
parseList (ParenEnd _ : ts) = return ([], ts)
parseList ts = do
  (x, ts') <- parse' ts
  (xs, ts'') <- parseList ts'
  return (x : xs, ts'')

parse' :: [Token] -> ParserResult (AST, [Token])
parse' (SymbolT sym pos : ts) = return (ast, ts)
  where
    ast :: AST
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

parseToAST :: String -> ParserResult AST
parseToAST s = fst <$> (parse' . flip evalState (Pos 0 0) $ tokenize s)

parse :: String -> ParserResult Term
parse s = astToTerm =<< parseToAST s

readType :: AST -> ParserResult Ty
readType (Symbol "Nat" _) = return (BaseTy Nat)
readType (List (Symbol "->" pos : tys) _)
  | length tys < 2 = Left (MalformedType, pos)
  | otherwise = return . typesToArrow =<< sequence (map readType tys)
  where
    typesToArrow :: [Ty] -> Ty
    typesToArrow (t:t':[]) = Arrow t t'
    typesToArrow (t:ts) = Arrow t (typesToArrow ts)
    typesToArrow [] = undefined
readType ast = Left (MalformedType, astPos ast)

astToTerm :: AST -> ParserResult Term
astToTerm (Symbol "+" _) = return (Constant Plus2)
astToTerm (Symbol s _) | length s == 1 = return (Var (head s) Nothing)
astToTerm (Symbol _ pos) = Left (LengthyVar, pos)
astToTerm (Quesito.Parse.Num x _) = return (Constant (C.Num x))
astToTerm (List [Symbol "lambda" _, List [Symbol s _, tyS] _, tS] _) | length s == 1 = do
  ty <- readType tyS
  t <- astToTerm tS
  return (Lambda v ty t)
  where
    v = head s
astToTerm (List [t, t'] _) = do
  t'' <- astToTerm t
  t''' <- astToTerm t'
  return (App t'' t''')
astToTerm (List _ pos) = Left (MultipleArguments, pos)
