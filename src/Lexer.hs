module Lexer where

import Data.Char

data Token
     = TokenAnd
     | TokenOr
     | TokenSymbol String
     | TokenString String
     | TokenVariable String
     | TokenPeriod
     | TokenComma
     | TokenLParen
     | TokenRParen
     | TokenImplies
  deriving (Show, Eq)

parseError :: [Token] -> a
parseError t = error ("Parse Error: " ++ show t)

getTokenString :: Token -> String
getTokenString (TokenString s) = s
getTokenString t = error ("Tried to get string from non-TokenString "++show t)

getTokenSymbol :: Token -> String
getTokenSymbol (TokenSymbol s) = s
getTokenSymbol t = error ("Tried to get string from non-TokenSymbol "++show t)

getTokenVariable :: Token -> String
getTokenVariable (TokenVariable s) = s
getTokenVariable t = error ("Tried to get string from non-TokenVariable "++show t)

isSymbolStart :: Char -> Bool
isSymbolStart c = isAlpha c || c == '_' || c == '-'

isSymbolChar :: Char -> Bool
isSymbolChar c = isSymbolStart c || isDigit c

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isSymbolStart c = lexSymbol (c:cs)
      | c == '?' = lexVariable cs
      | c == '"' = lexString cs []
      | c == ':' = lexImplies cs
lexer ('.':cs) = TokenPeriod : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer ('(':cs) = TokenLParen : lexer cs
lexer (')':cs) = TokenRParen : lexer cs
lexer cs = error ("Unexpected token at "++cs)

lexImplies [] = fail "Expected - after :"
lexImplies ('-':cs) = TokenImplies : lexer cs
lexImplies _ = fail "Expected - after :"

lexReadSymbol = takeWhile isSymbolChar

lexSymbol l =
  let s = lexReadSymbol l in
  if s == "and" then
    TokenAnd : lexer (drop (length s) l)
  else if s == "or" then
    TokenOr : lexer (drop (length s) l)
  else
    TokenSymbol s : lexer (drop (length s) l)

lexVariable l =
  let s = lexReadSymbol l in
  TokenVariable s : lexer (drop (length s) l)

lexString [] acc = [TokenString $ reverse acc]
lexString ('"':'"':l) acc = lexString l ('"':acc)
lexString ('"':l) acc = TokenString (reverse acc) : lexer l
lexString (lc:l) acc = lexString l (lc:acc)
