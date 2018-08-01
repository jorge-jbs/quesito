module Quesito.Parse
  ( Quesito.Parse.parse
  )
where


import Quesito.TT (CheckTerm(..), InfTerm(..), Const(..))

import Text.Parsec ((<|>), try, parse, parserFail)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Prim (many)
import Text.Parsec.Combinator (many1)
import Text.Parsec.Char (char, digit, letter, spaces, space, string, oneOf)
import Text.Parsec.String (Parser)


number :: Parser Int

number = do
  str <- many1 digit
  return (read str)


symbol :: Parser String

symbol = do
  c <- letter <|> oneOf "+_"
  cs <- many (letter <|> digit <|> oneOf "+_")
  return (c : cs)


lambda :: Parser CheckTerm

lambda = do
  _ <- char '\\'
  spaces
  var <- symbol
  spaces
  _ <- string "->"
  spaces
  expr <- checkTerm False
  return (Lam var expr)


typeUniv :: Parser InfTerm

typeUniv = do
  _ <- string "Type"
  _ <- many1 space
  level <- number
  return (Type level)


piExpr :: Parser InfTerm

piExpr = do
  _ <- char '('
  spaces
  var <- symbol
  spaces
  _ <- char ':'
  spaces
  ty <- infTerm False
  spaces
  _ <- char ')'
  spaces
  _ <- string "->"
  spaces
  ty' <- infTerm False
  return (Pi var ty ty')


app :: Parser InfTerm
app = do
  e <- infTerm True
  _ <- many1 space
  e' <- checkTerm True
  return (App e e')


ann :: Parser InfTerm
ann = do
  e <- checkTerm True
  spaces
  _ <- char ':'
  spaces
  e' <- infTerm False
  return (Ann e e')

surround :: Parser a -> Parser a

surround p = do
  _ <- char '('
  spaces
  e <- p
  spaces
  _ <- char ')'
  return e


surrIf :: Bool -> Parser a -> Parser a

surrIf True =
  surround

surrIf False =
  id


infTerm :: Bool -> Parser InfTerm

infTerm surrounded
    = try (surrIf surrounded typeUniv)
  <|> try (surrIf surrounded app)
  <|> try (surrIf surrounded piExpr)
  <|> try (surrIf surrounded ann)
  <|> (Constant . Int <$> try number)
  <|> (Var <$> try symbol)


checkTerm :: Bool -> Parser CheckTerm

checkTerm surrounded
    = try (surrIf surrounded lambda)
  <|> (Inf <$> infTerm surrounded)


annotation :: Parser (String, CheckTerm)

annotation = do
  name <- symbol
  spaces
  _ <- char ':'
  spaces
  ty <- checkTerm False
  _ <- char ';'
  return (name, ty)


implementation :: Parser (String, CheckTerm)

implementation = do
  spaces
  name <- symbol
  spaces
  _ <- char '='
  spaces
  body <- checkTerm False
  spaces
  _ <- char ';'
  spaces
  return (name, body)


definition :: Parser (String, CheckTerm, CheckTerm)

definition = do
  spaces
  (name, ty) <- annotation
  spaces
  (name', body) <- implementation
  spaces
  if name == name' then
    return (name, ty, body)
  else
    parserFail ("Expecting implementation for \"" ++ name ++ "\" but found for \"" ++ show name ++ "\".")


parse :: String -> Either ParseError [(String, CheckTerm, CheckTerm)]

parse =
  Text.Parsec.parse (many definition) ""

