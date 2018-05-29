
data AST
  = Symbol String
  | Num Int
  | List [AST]
  deriving (Show)

data Token
  = ParenBegin
  | ParenEnd
  | SymbolT String
  deriving (Show)

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace ',' = True
isWhitespace _ = False

isDelimiter :: Char -> Bool
isDelimiter '(' = True
isDelimiter ')' = True
isDelimiter c = isWhitespace c

tokenize :: String -> [Token]
tokenize [] = []
tokenize (' ' : str) = tokenize str
tokenize (',' : str) = tokenize str
tokenize ('(' : str) = ParenBegin : tokenize str
tokenize (')' : str) = ParenEnd : tokenize str
tokenize str = SymbolT (takeWhile (not . isDelimiter) str) : tokenize (dropWhile (not . isDelimiter) str)

parseList :: [Token] -> ([AST], [Token])
parseList (ParenEnd : ts) = ([], ts)
parseList ts =
  let
    (x, ts') = parse ts
    (xs, ts'') = parseList ts'
  in
    (x : xs, ts'')

parse :: [Token] -> (AST, [Token])
parse (SymbolT sym : ts) = (Symbol sym, ts)
parse (ParenBegin : ts) =
  let
    (xs, ts') = parseList ts
  in
    (List xs, ts')
parse [] = undefined
parse (ParenEnd : _) = undefined

main = do
  putStrLn "hue"
