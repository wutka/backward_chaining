module Main where

import Parser
import Lexer
import BackChain

main :: IO ()
main = do
  f <- readFile "data.txt"
  print $ parser (lexer f)
