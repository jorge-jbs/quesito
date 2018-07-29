module Quesito.Parse
  ( parse
  , ParseError
  , ParserResult
  , Pos
  ) where

import Control.Monad.State (State, evalState, modify, get)

import Quesito.TT

data ParseError
  = MismatchedParenthesis
  | ReachedEndOfFile
  | MalformedType
  | MalformedDefinition
  | MultipleArguments
  | FreeVar
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

parse :: String -> ParserResult [(Name, CheckTerm, CheckTerm)]
parse = fmap reverse . parse_ [] [] . flip evalState (Pos 0 0) . tokenize
  where
    parse_ :: [Name] -> [(Name, CheckTerm, CheckTerm)] -> [Token] -> ParserResult [(Name, CheckTerm, CheckTerm)]
    parse_ _ defs [] = return defs
    parse_ freeScope defs ts = do
      (defS, ts') <- parse' ts
      def@(name, _, _) <- parseDefinition freeScope defS
      parse_ (name : freeScope) (def : defs) ts'

parseDefinition :: [Name] -> SExpr -> ParserResult (Name, CheckTerm, CheckTerm)
parseDefinition freeScope (List [Symbol "define" _, Symbol name _, tyS, tS] _) = do
  ty <- sexpToTerm freeScope tyS
  t <- sexpToTerm freeScope tS
  return (name, ty, t)
parseDefinition freeScope sexp =
  Left (MalformedDefinition, astPos sexp)

sexpToTerm :: [Name] -> SExpr -> ParserResult CheckTerm
sexpToTerm freeScope = sexpToTerm' []
  where
    sexpToTerm' :: [Name] -> SExpr -> ParserResult CheckTerm
    sexpToTerm' scope (Symbol "+" _) = return (Inf (Constant Plus))
    sexpToTerm' scope (Symbol "Int" _) = return (Inf (Constant IntType))
    sexpToTerm' scope (Symbol s pos) =
      if elem s scope || elem s freeScope then
        return (Inf (Var s))
      else
        Left (FreeVar, pos)
    sexpToTerm' _ (Quesito.Parse.Num n _) = return (Inf (Constant (Int n)))
    sexpToTerm' scope (List [Symbol "lambda" _, List [Symbol s _] _, tS] _) = do
      t <- sexpToTerm' (s : scope) tS
      return (Lam s t)
    sexpToTerm' scope (List [Symbol "pi" _, List [Symbol s _, tS] _, tS'] _) = do
      Inf t <- sexpToTerm' scope tS
      Inf t' <- sexpToTerm' (s : scope) tS'
      return (Inf (Pi s t t'))
    sexpToTerm' scope (List [Symbol "Type" _, Quesito.Parse.Num i _] _) = return (Inf (Type i))
    sexpToTerm' scope (List [Symbol "ann" _, tS, tS'] _) = do
      t <- sexpToTerm' scope tS
      Inf t' <- sexpToTerm' scope tS'
      return (Inf (Ann t t'))
    sexpToTerm' scope (List [t, t'] _) = do
      Inf t'' <- sexpToTerm' scope t
      t''' <- sexpToTerm' scope t'
      return (Inf (App t'' t'''))
    sexpToTerm' _ (List _ pos) = Left (MultipleArguments, pos)
