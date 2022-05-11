module Main where

import System.IO
import BackChain
import Loader
import qualified Data.Map as Map

promptLoop :: KnowledgeBase -> IO ()
promptLoop kb = do
  putStr "Enter query: "
  hFlush stdout
  q <- getLine
  if q /= ":quit" then do
    a <- parseAssertion q
    if not $ null (proveConsequent kb (assertionToConsequent a) Map.empty) then
      putStrLn "True"
    else
      putStrLn "False"
    promptLoop kb
  else
    return ()
    
    
    
    
  
main :: IO ()
main = do
  kb <- loadFile "data.txt"
  promptLoop kb
