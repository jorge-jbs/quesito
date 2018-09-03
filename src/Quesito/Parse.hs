module Quesito.Parse (Quesito.Parse.parse) where

import Quesito.TT (Term(..), TermKind(..), Pos(..), Decl(..), Name)

import Control.Monad (when)
import Data.Foldable (foldlM)
import Data.Functor.Identity (Identity)
import Text.Parsec
  ( SourcePos, (<|>), try, parse, parserFail, eof, alphaNum, letter, oneOf
  , spaces, char, string, space, getPosition, sourceLine, sourceColumn, sepBy
  , option
  )
import Text.Parsec.Combinator (many1)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Expr (buildExpressionParser , Operator(..) , Assoc(..))
import Text.Parsec.Prim (many)
import Text.Parsec.String (Parser)
import Text.Parsec.Token
  ( GenTokenParser(..), GenLanguageDef(..), commentStart, commentEnd
  , commentLine, nestedComments, identStart, identLetter, opStart, opLetter
  , reservedNames, reservedOpNames, caseSensitive, makeTokenParser
  )

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
                    Term pos (Ann (Term _ (Bound x)) ty) ->
                      Term pos (Pi x ty b)
                    Term pos _ ->
                      Term pos (Pi "" a b)
                )
            )
            AssocRight
        ]
      , [ Infix (reservedOp tp ":" >> return (\a@(Term pos _) b -> Term pos (Ann a b))) AssocLeft ]
      ]

expr :: Parser (Term Name)
expr =
    try appParser
    <|> try typeParser
    <|> try (parens tp raw)
    <|> try lambdaParser
    <|> nonParen

attachPos :: Parser (TermKind Name) -> Parser (Term Name)
attachPos f = do
  pos <- pPosToQPos <$> getPosition
  Term pos <$> f

typeParser :: Parser (Term Name)
typeParser =
  attachPos
    (try (reserved tp "Type" >> natural tp >>= \i -> return (Type (fromIntegral i)))
    <|> (reserved tp "Type" >> return (Type 0)))

lambdaParser :: Parser (Term Name)
lambdaParser =
  attachPos (do reservedOp tp "\\"; x <- identifier tp; reservedOp tp "->"; body <- raw; return (Lam x body))

nonParen :: Parser (Term Name)
nonParen = do
  pos <- pPosToQPos <$> getPosition
  try (fmap (Term pos . Bound) (identifier tp))

appParser :: Parser (Term Name)
appParser = do
  e@(Term pos _) <- nonParen <|> parens tp raw
  es <- many1 (nonParen <|> parens tp raw)
  foldlM (\acc x -> return (Term pos (App acc x))) e es

pPosToQPos :: SourcePos -> Pos
pPosToQPos pos =
  Pos (sourceLine pos) (sourceColumn pos)

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
      , reservedNames = ["data", "where", "Type", "->"]
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

matchFunctionParser :: Name -> Parser [([(Name, Term Name)], Term Name, Term Name)]
matchFunctionParser name = do
  defs <- many1 (try matchFunctionCaseParser)
  when (any (\(name', _, _, _) -> name /= name') defs) (parserFail ("definition of " ++ name))
  spaces
  return (map (\(_, y, z, w) -> (y, z, w)) defs)

matchFunctionCaseParser :: Parser (Name, [(Name, Term Name)], Term Name, Term Name)
matchFunctionCaseParser = do
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
    findName (Term _ (App e _)) =
      findName e
    findName (Term _ (Bound x)) =
      Just x
    findName _ =
      Nothing

matchFunctionDefinition :: Parser Decl
matchFunctionDefinition = do
  spaces
  (name, ty) <- annotation True
  spaces
  defs <- matchFunctionParser name
  spaces
  return (MatchFunctionDecl name defs ty)

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
       decls <- many (try matchFunctionDefinition <|> try definition <|> typeDecl)
       eof
       return decls
    )
    ""
