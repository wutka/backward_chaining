module Main where

import System.IO
import BackChain
import Loader
import qualified Data.Map as Map
import Data.List
import Data.Char

printAssertions :: KnowledgeBase -> IO ()
printAssertions (KnowledgeBase assertions _) =
  putStrLn $ unlines $ zipWith printAssertion assertions [1..]
  where
    printAssertion a n = show n++": "++show a

printRules :: KnowledgeBase -> IO ()
printRules (KnowledgeBase _ rules) =
  putStrLn $ unlines $ zipWith printRule rules [1..]
  where
    printRule r n = show n++": "++show r

addAssertions :: KnowledgeBase -> IO KnowledgeBase
addAssertions kb@(KnowledgeBase assertions rules) = do
  putStr "Enter assertion: "
  hFlush stdout
  q <- getLine
  if null q then
    return kb
  else do
    a <- parseAssertion q
    addAssertions $ KnowledgeBase (assertions++[a]) rules
 
addRules :: KnowledgeBase -> IO KnowledgeBase
addRules kb@(KnowledgeBase assertions rules) = do
  putStr "Enter rules: "
  hFlush stdout
  q <- getLine
  if null q then
    return kb
  else do
    r <- parseRule q
    addRules $ KnowledgeBase assertions (rules ++ [r])

saveFile :: String -> KnowledgeBase -> IO ()
saveFile filename (KnowledgeBase assertions rules) =
  writeFile filename $ unlines $ map show assertions ++ map show rules

showHelp :: IO ()
showHelp = do
  putStrLn "Enter an assertion to be proved, or one of the following commands:"
  putStrLn ":a    -  List assertions"
  putStrLn ":r    -  List rules"
  putStrLn "+a    -  Start adding new assertions (blank line when done)"
  putStrLn "+r    -  Start adding new rules (blank line when done)"
  putStrLn "-an   -  Delete assertion n (numbered starting at 1)"
  putStrLn "-rn   -  Delete rule n (numbered starting at 1)"
  putStrLn ":save -  Save to file (system will prompt for filename)"
  putStrLn ":load -  Load from file (system will prompt for filename)"
  putStrLn ":new  -  Start with new empty knowledge base"
  putStrLn ":quit -  Quit"
  putStrLn ":help -  Display this help information"
  
printAllMatches :: Consequent -> [SearchContext] -> IO ()
printAllMatches c sc = do

  putStrLn $ unlines $ filter (not . null) $ map printConsequent (nub $ map getVM sc)
  where
    getVM (SearchContext vm _) = vm
    printConsequent vm = if isConstantConsequent $ updatedConsequent vm then show $ updatedConsequent vm else ""
    updatedConsequent vm = applyMapToConsequent c vm
    
promptLoop :: KnowledgeBase -> IO ()
promptLoop kb@(KnowledgeBase assertions rules) = do
  putStr "Enter query: "
  hFlush stdout
  q <- getLine
  if q == ":a" then do
    printAssertions kb
    promptLoop kb
  else if q == ":r" then do
    printRules kb
    promptLoop kb
  else if q == "+a" then do
    newKb <- addAssertions kb
    promptLoop newKb
  else if q == "+r" then do
    newKb <- addRules kb
    promptLoop newKb
  else if length q > 2 && take 2 q == "-a" then do
    let aNum = read $ dropWhile isSpace (drop 2 q)
    let newA = take (aNum-1) assertions ++ drop aNum assertions
    promptLoop (KnowledgeBase newA rules)
  else if length q > 2 && take 2 q == "-r" then do
    let rNum = read $ dropWhile isSpace (drop 2 q)
    let newR = take (rNum-1) rules ++ drop rNum rules
    promptLoop (KnowledgeBase assertions newR)
  else if q == ":save" then do
    putStr "Save to file: "
    hFlush stdout
    filename <- getLine
    saveFile filename kb
    promptLoop kb
  else if q == ":load" then do
    putStr "Load from file: "
    hFlush stdout
    filename <- getLine
    newKb <- loadFile filename
    promptLoop newKb
  else if q == ":new" then
    promptLoop (KnowledgeBase [] [])
  else if q == ":help" then do
    showHelp
    promptLoop kb
  else if q /= ":quit" then do
    c <- parseQuery q
    let result = proveConsequent kb c (SearchContext Map.empty [])
    if not $ null result then
      if isConstantConsequent c then
        putStrLn "True"
      else
        printAllMatches c (nub result)
    else
      putStrLn "False"
    promptLoop kb
  else
    return ()    
  
main :: IO ()
main = do
  kb <- loadFile "data.txt"
  putStrLn "Welcome to Backchain. (:help for help)"
  promptLoop kb
