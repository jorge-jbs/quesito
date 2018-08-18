module Quesito.Parse
  ( Quesito.Parse.parse
  )
where


import Quesito.TT (Term(..), Decl(..), Name)

import Control.Monad (when)
import Data.Foldable (foldlM)
import Text.Parsec ((<|>), try, parse, parserFail, eof, alphaNum, letter, oneOf, spaces, char, string, space)
import Text.Parsec.Combinator (many1)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Expr
import Text.Parsec.Prim (many)
import Text.Parsec.String (Parser)
import Text.Parsec.Token


raw :: Parser (Term Name)
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
                    Ann (Bound x) ty ->
                      Pi x ty b
                    _ ->
                      Pi "" a b
                )
            )
            AssocRight
        ]
      , [ Infix (reservedOp tp ":" >> return (\a b -> Ann a b)) AssocLeft ]
      ]

    expr =
      try appParser
      <|> try (reserved tp "Type" >> natural tp >>= \i -> return (Type (fromIntegral i)))
      <|> try (parens tp raw)
      <|> try (do reservedOp tp "\\"; x <- identifier tp; reservedOp tp "->"; body <- raw; return (Lam x body))
      <|> nonParen

    nonParen =
      try (fmap Bound (identifier tp))
      <|> try (reserved tp "fix" >> return Fix)

    appParser = do
      e <- nonParen <|> parens tp raw
      es <- many1 (nonParen <|> parens tp raw)
      foldlM (\acc x -> return (App acc x)) e es

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
          , reservedNames = ["data", "where", "Type", "fix", "->"]
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


annotation :: Bool -> Parser (Name, Term Name)
annotation semicolon = do
  name <- identifier'
  spaces
  _ <- char ':'
  spaces
  ty <- raw
  spaces
  when semicolon (char ';' >> return ())
  return (name, ty)


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


implementation :: Parser (Name, Term Name)
implementation = do
  spaces
  name <- identifier'
  spaces
  _ <- char '='
  spaces
  body <- raw
  _ <- char ';'
  return (name, body)


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
