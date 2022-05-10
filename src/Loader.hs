module Loader where

import BackChain
import Parser
import Lexer
import Data.Either

makeKnowledgeBase :: [Either Assertion Rule] -> KnowledgeBase
makeKnowledgeBase parsed = KnowledgeBase (lefts parsed) (rights parsed)

loadFile :: String -> IO KnowledgeBase
loadFile filename = do
  contents <- readFile filename
  let parsed = parser (lexer contents)
  return $ makeKnowledgeBase parsed

parseAssertion :: String -> IO Assertion
parseAssertion s = do
  let parsed = parser (lexer $ addPeriod s)
  return $ head (lefts parsed)
  where
    addPeriod s = if last s == '.' then s else s ++ ['.']
    
