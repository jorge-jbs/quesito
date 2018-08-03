module Quesito.Parse
  ( Quesito.Parse.parse
  )
where


import Quesito.TT (CheckTerm(..), InfTerm(..), Const(..), Def(..), Name)

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
  c <- letter <|> oneOf operatorCharacters
  cs <- many (letter <|> digit <|> oneOf operatorCharacters)
  if any (not . flip elem operatorCharacters) (c : cs) then
    return (c : cs)
  else
    parserFail "Expected symbol, found operator."


operatorCharacters :: [Char]

operatorCharacters =
  "!#$%&*+./<=>?@\\^|-~"


operator :: Parser String

operator = do
  str <- many1 (oneOf operatorCharacters)
  if elem str ["->", ":"] then
    parserFail ("Reserved operator: " ++ str)
  else
    return str


var :: String -> InfTerm

var "+" =
  Constant Plus

var "Int" =
  Constant IntType

var s =
  Var s


lambda :: Parser CheckTerm

lambda = do
  _ <- char '\\'
  spaces
  v <- symbol
  spaces
  _ <- string "->"
  spaces
  expr <- checkTerm False
  return (Lam v expr)


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
  v <- symbol
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
  return (Pi v ty ty')


infixApp :: Parser InfTerm

infixApp = do
  e <-  try (surround lambda)
    <|> try (Inf <$>
           (    try typeUniv
            <|> try app
            <|> try piExpr
            <|> try ann
            <|> (Constant . Int <$> try number)
            <|> (var <$> try symbol)
           )
        )
  spaces
  op <- operator
  spaces
  e' <- checkTerm False
  return (App (App (var op) e) e')


app :: Parser InfTerm
app = do
  e <- infTerm True
  es <- many1 (try (many1 space >> checkTerm True))
  return (curryApp e es)
  where
    curryApp :: InfTerm -> [CheckTerm] -> InfTerm

    curryApp e (e' : []) =
      App e e'

    curryApp e (e' : es) =
      curryApp (App e e') es


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
  <|> try (surrIf surrounded infixApp)
  <|> try (surrIf surrounded app)
  <|> try (surrIf surrounded piExpr)
  <|> try (surrIf surrounded ann)
  <|> (Constant . Int <$> try number)
  <|> (var <$> try symbol)


checkTerm :: Bool -> Parser CheckTerm

checkTerm surrounded
    = try (surrIf surrounded lambda)
  <|> (Inf <$> infTerm surrounded)


annotation :: Parser (Name, InfTerm)

annotation = do
  name <- symbol
  spaces
  _ <- char ':'
  spaces
  ty <- infTerm False
  _ <- char ';'
  return (name, ty)


implementation :: Parser (Name, CheckTerm)

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


definition :: Parser (Name, Def CheckTerm InfTerm)

definition = do
  spaces
  (name, ty) <- annotation
  spaces
  (name', body) <- implementation
  spaces
  if name == name' then
    return (name, DExpr body ty)
  else
    parserFail ("Expecting implementation for \"" ++ name ++ "\" but found for \"" ++ show name ++ "\".")


parse :: String -> Either ParseError [(Name, Def CheckTerm InfTerm)]

parse =
  Text.Parsec.parse (many definition) ""
