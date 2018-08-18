module Quesito.Parse
  ( Quesito.Parse.parse
  )
where


import Quesito.TT (CheckTerm(..), InfTerm(..), Decl(..), Name)

import Control.Monad (when)
import Data.Foldable (foldlM)
import Text.Parsec ((<|>), try, parse, parserFail, eof, alphaNum, letter, oneOf, spaces, char, string, space)
import Text.Parsec.Combinator (many1)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Expr
import Text.Parsec.Prim (many)
import Text.Parsec.String (Parser)
import Text.Parsec.Token


data Raw
  = RBound Name
  | RFree Name
  | RType Int
  | RPi Name Raw Raw
  | RApp Raw Raw
  | RLam Name Raw
  | RAnn Raw Raw
  deriving (Show, Eq)


raw :: Parser Raw
raw =
  buildExpressionParser table expr
  where
    table =
      [ [ Infix
            (
              reservedOp tp "->" >>
              return
                (\a b ->
                  case a of
                    RAnn (RBound x) ty ->
                      RPi x ty b
                    _ ->
                      RPi "" a b
                )
            )
            AssocRight
        ]
      , [ Infix (reservedOp tp ":" >> return (\a b -> RAnn a b)) AssocLeft ]
      ]

    expr =
      try appParser
      <|> try (reserved tp "Type" >> natural tp >>= \i -> return (RType (fromIntegral i)))
      <|> try (parens tp raw)
      <|> try (do reservedOp tp "\\"; x <- identifier tp; reservedOp tp "->"; body <- raw; return (RLam x body))
      <|> nonParen

    nonParen =
      fmap RBound (identifier tp)

    appParser = do
      e <- nonParen <|> parens tp raw
      es <- many1 (nonParen <|> parens tp raw)
      foldlM (\acc x -> return (RApp acc x)) e es

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
          , reservedNames = ["data", "where", "Type", "->"]
          , reservedOpNames = ["->", ":", "\\", ";"]
          , caseSensitive = True
          }


opLetter' :: Parser Char
opLetter' =
  oneOf "!#$%&*+./<=>?@\\^|-~"


identifier' :: Parser String
identifier' = do
  c <- letter <|> oneOf "-_"
  cs <- many (alphaNum <|> opLetter')
  return (c : cs)


rawToInf :: Raw -> Maybe InfTerm

rawToInf (RBound name) =
  Just (Bound name)

rawToInf (RFree name) =
  Just (Free name)

rawToInf (RType i) =
  Just (Type i)

rawToInf (RPi x e e') = do
  t <- rawToInf e
  t' <- rawToInf e'
  return (Pi x t t')

rawToInf (RApp e e') = do
  t <- rawToInf e
  t' <- rawToCheck e'
  return (App t t')

rawToInf (RLam _ _) =
  Nothing

rawToInf (RAnn e e') = do
  t <- rawToCheck e
  t' <- rawToInf e'
  return (Ann t t')


rawToCheck :: Raw -> Maybe CheckTerm

rawToCheck e =
  case rawToInf e of
    Just t ->
      Just (Inf t)

    Nothing ->
      case e of
        RLam x e' -> do
          t' <- rawToCheck e'
          return (Lam x t')

        _ ->
          Nothing


annotation :: Bool -> Parser (Name, InfTerm)
annotation semicolon = do
  name <- identifier'
  spaces
  _ <- char ':'
  spaces
  ty <- raw
  case rawToInf ty of
    Just ty' -> do
      spaces
      when semicolon (char ';' >> return ())
      return (name, ty')

    Nothing ->
      parserFail "inferable expression"


typeDecl :: Parser Decl
typeDecl = do
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
  return (TypeDecl name ty conss)


implementation :: Parser (Name, CheckTerm)
implementation = do
  spaces
  name <- identifier'
  spaces
  _ <- char '='
  spaces
  body <- raw
  case rawToCheck body of
    Just body' -> do
      _ <- char ';'
      return (name, body')

    Nothing ->
      parserFail "type checkable expression"


definition :: Parser Decl
definition = do
  spaces
  (name, ty) <- annotation True
  spaces
  (name', body) <- implementation
  spaces
  if name == name' then
    return (ExprDecl name body ty)
  else
    parserFail ("Expecting implementation for \"" ++ name ++ "\" but found for \"" ++ show name ++ "\".")


parse :: String -> Either ParseError [Decl]
parse =
  Text.Parsec.parse
    (do
       decls <- many (try definition <|> typeDecl)
       eof
       return decls
    )
    ""
