module Quesito.Parse (Quesito.Parse.parse) where

import Quesito
import Quesito.TT (Term(..), mapInLoc, remLoc, Name)
import Quesito.TT.TopLevel (Decl(..), getNames)

import Control.Monad (when)
import Data.Foldable (foldlM)
import Data.Functor.Identity (Identity)
import Text.Parsec
  ( Parsec, SourcePos, (<|>), try, parserFail, eof, alphaNum, letter , oneOf
  , space, spaces, string, char, getPosition, sourceLine, sourceColumn, sepBy, option
  , runParser, putState, getState, optionMaybe
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

type Parser = Parsec String [Name]

withEnv :: Parser a -> [Name] -> Parser a
withEnv m name = do
  env <- getState
  putState (name ++ env)
  x <- m
  putState env
  return x

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
                   mapInLoc
                     a
                     (\a' ->
                        case a' of
                          Ann v ty ->
                            case remLoc v of
                              Local u ->
                                Pi u ty b
                              _ ->
                                Pi "" a b
                          _ ->
                            Pi "" a b
                     )
                )
            )
            AssocRight
        ]
      , [ Infix (reservedOp tp ":" >> return (\a b -> Ann a b)) AssocLeft ]
      ]

expr :: Parser (Term Name)
expr =
    try appParser
    <|> try typeParser
    <|> try (parens tp raw)
    <|> try lambdaParser
    <|> nonParen

attachPos :: Parser (Term Name) -> Parser (Term Name)
attachPos x = do
  loc <- pPosToQPos <$> getPosition
  Loc loc <$> x
  where
    pPosToQPos :: SourcePos -> Location
    pPosToQPos loc =
      Location (sourceLine loc) (sourceColumn loc)

typeParser :: Parser (Term Name)
typeParser =
  attachPos
    (try (reserved tp "Type" >> natural tp >>= \i -> return (Type (fromIntegral i)))
    <|> try (reserved tp "Type" >> return (Type 0))
    <|> (reserved tp "Bytes" >> natural tp >>= \i -> return (BytesType (fromIntegral i))))

lambdaParser :: Parser (Term Name)
lambdaParser = attachPos $ do
  reservedOp tp "\\"
  x <- identifier tp
  reservedOp tp "->"
  body <- raw
  return (Lam x body)

nonParen :: Parser (Term Name)
nonParen = getState >>= \env ->
  attachPos
    (try (do
      v <- identifier tp
      if v `elem` env then
        return (Global v)
      else
        return (Local v)
    )
    <|> (Num . fromIntegral <$> natural tp)
    )

appParser :: Parser (Term Name)
appParser = attachPos $ do
  e <- try nonParen <|> parens tp raw
  es <- many1 (try nonParen <|> parens tp raw)
  foldlM (\acc x -> return (App acc x)) e es

tp :: GenTokenParser String [Name] Identity
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
      , reservedNames = ["data", "where", "Type", "Bytes", "->"]
      , reservedOpNames = ["->", ":", "\\", ";", "," , "."]
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
    (name', ty') <- annotation True `withEnv` [name]
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

patternMatchingParser :: Name -> Parser [([(Name, Term Name)], Term Name, Term Name)]
patternMatchingParser name = do
  defs <- many1 (try patternMatchingCaseParser)
  when (any (\(name', _, _, _) -> name /= name') defs) (parserFail ("definition of " ++ name))
  spaces
  return (map (\(_, y, z, w) -> (y, z, w)) defs)

patternMatchingCaseParser :: Parser (Name, [(Name, Term Name)], Term Name, Term Name)
patternMatchingCaseParser = do
  vars <- option [] $ do
    spaces
    vars <- try (annotation False) `sepBy` try (spaces >> char ',' >> spaces)
    spaces
    _ <- char '.'
    spaces
    return vars
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
  return (name, vars, lhs, rhs)
  where
    findName :: Term Name -> Maybe Name
    findName (App e _) =
      findName e
    findName (Local x) =
      Just x
    findName (Loc _ e) =
      findName e
    findName _ =
      Nothing

patternMatchingDefinition :: Parser Decl
patternMatchingDefinition = do
  spaces
  (name, ty) <- annotation True
  spaces
  defs <- patternMatchingParser name
  spaces
  return (PatternMatchingDecl name defs ty)

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

parseDeclarations :: Parser [Decl]
parseDeclarations = do
  maybeDecl <- optionMaybe (try definition <|> try patternMatchingDefinition <|> typeDecl)
  case maybeDecl of
    Just decl ->
      (decl :) <$> parseDeclarations `withEnv` getNames decl
    Nothing ->
      eof >> return []

parse :: String -> Either ParseError [Decl]
parse =
  runParser parseDeclarations [] ""
