module Quesito.Syntax.Parse (Quesito.Syntax.Parse.parse) where

import Quesito
import Quesito.Syntax
import Quesito.TT (Flags(..))

import Control.Monad (when)
import Data.Functor.Identity (Identity)
import Data.Maybe (isJust)
import Text.Parsec
  ( Parsec, (<|>), try, parserFail, eof, alphaNum, letter, oneOf, space
  , spaces, string, char, getPosition, sourceLine, sourceColumn, runParser
  , optionMaybe
  )
import Text.Parsec.Combinator (many1)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Expr (buildExpressionParser , Operator(..) , Assoc(..))
import Text.Parsec.Prim (many)
import Text.Parsec.Token
  ( GenTokenParser(..), GenLanguageDef(..), commentStart, commentEnd
  , commentLine, nestedComments, identStart, identLetter, opStart, opLetter
  , reservedNames, reservedOpNames, caseSensitive, makeTokenParser
  )

type Parser = Parsec String ()

raw :: Parser Term
raw =
  buildExpressionParser table expr
  where
    table =
      [ [ Infix (reservedOp tp "->" >> return Arrow) AssocRight ]
      , [ Infix (reservedOp tp ":" >> return Ann) AssocLeft ]
      ]

expr :: Parser Term
expr = do
  loc <- getPosition
  Loc (Location (sourceLine loc) (sourceColumn loc))
    <$> (
      try appParser
      <|> try (parens tp raw)
      <|> try lambdaParser
      <|> nonParen
    )

lambdaParser :: Parser Term
lambdaParser = do
  reservedOp tp "\\"
  x <- identifier tp
  reservedOp tp "->"
  body <- raw
  return (Lam x body)

nonParen :: Parser Term
nonParen =
  try (Var <$> identifier tp)
  <|> Num . fromIntegral <$> natural tp

appParser :: Parser Term
appParser = do
  App
    <$> (try nonParen <|> parens tp raw)
    <*> many1 (try nonParen <|> parens tp raw)

tp :: GenTokenParser String () Identity
tp =
  makeTokenParser
    LanguageDef
      { commentStart = "{-"
      , commentEnd = "-}"
      , commentLine = "--"
      , nestedComments = True
      , identStart = letter <|> oneOf "-_"
      , identLetter = alphaNum <|> opLetter'
      , opStart = opLetter'
      , opLetter = opLetter'
      , reservedNames = ["data", "where", "->"]
      , reservedOpNames = ["->", ":", "\\", ";"]
      , caseSensitive = True
      }

opLetter' :: Parser Char
opLetter' =
  oneOf "!#$%&*+./<=>?@\\^|-~'"

identifier' :: Parser String
identifier' = do
  c <- letter <|> oneOf "-_"
  cs <- many (alphaNum <|> opLetter')
  return (c : cs)

annotation :: Bool -> Parser (String, Term)
annotation semicolon = do
  name <- identifier'
  spaces
  _ <- char ':'
  spaces
  ty <- raw
  spaces
  when semicolon (char ';' >> return ())
  return (name, ty)

typeDef :: Parser Def
typeDef = do
  spaces
  _ <- string "data"
  _ <- many1 space
  (name, ty) <- annotation False
  spaces
  _ <- string "where"
  spaces
  _ <- char '{'
  conss <- many $ try $ do
    spaces
    (name', ty') <- annotation True
    return (name', ty')
  spaces
  _ <- char '}'
  return (TypeDef name ty conss)

patternMatchingParser :: String -> Parser [(Term, Term)]
patternMatchingParser name = do
  defs <- many1 (try patternMatchingCaseParser)
  when (any (\(name', _, _) -> name /= name') defs) (parserFail ("definition of " ++ name))
  spaces
  return (map (\(_, y, z) -> (y, z)) defs)

patternMatchingCaseParser :: Parser (String, Term, Term)
patternMatchingCaseParser = do
  spaces
  lhs <- raw
  spaces
  name <-
    case findName lhs of
      Just x ->
        return x
      Nothing ->
        parserFail "function name"
  spaces
  _ <- char '='
  spaces
  rhs <- raw
  spaces
  _ <- char ';'
  spaces
  return (name, lhs, rhs)
  where
    findName (Loc _ t) =
      findName t
    findName (App t _) =
      findName t
    findName (Var x) =
      Just x
    findName _=
      Nothing

patternMatchingDef :: Parser Def
patternMatchingDef = do
  spaces
  isTotal <- isJust <$> optionMaybe (string "#total")
  spaces
  (name, ty) <- annotation True
  spaces
  defs <- patternMatchingParser name
  spaces
  return (PatternMatchingDef name defs ty (Flags isTotal))

definitions :: Parser [Def]
definitions = do
  maybeDef <- optionMaybe (try patternMatchingDef <|> typeDef)
  case maybeDef of
    Just decl ->
      (decl :) <$> definitions
    Nothing ->
      eof >> return []

parse :: String -> Either ParseError [Def]
parse =
  runParser definitions () ""
