module BackChain where

import Data.Either
import Data.Maybe
import qualified Data.Map as Map

data RuleValue =
    RuleConstant String
  | RuleVariable String
  deriving (Show, Eq)

data Assertion =
  Assertion String [String]
  deriving (Show, Eq)

data Antecedent =
    SimpleExpr String [RuleValue]
  | AndExpr Antecedent Antecedent
  | OrExpr Antecedent Antecedent
  deriving (Show, Eq)

data Consequent =
    Consequent String [RuleValue]
  deriving (Show, Eq)

data Rule =
    Rule Antecedent [Consequent]
  deriving (Show, Eq)

data KnowledgeBase =
    KnowledgeBase [Assertion] [Rule]
  deriving (Show, Eq)


type VarMap = Map.Map String String

assertionToConsequent :: Assertion -> Consequent
assertionToConsequent (Assertion name vs) =
  Consequent name (map RuleConstant vs)


assertionValueMatch :: String -> RuleValue -> Bool
assertionValueMatch s (RuleConstant s2) = s == s2
assertionValueMatch _ (RuleVariable _) = True

matchAssertion :: Consequent -> Assertion -> Bool
matchAssertion (Consequent cName cs) (Assertion aName as) =
  aName == cName && and (zipWith assertionValueMatch as cs)

consequentValueMatch :: RuleValue -> RuleValue -> Bool
consequentValueMatch (RuleConstant c1) (RuleConstant c2) = c1 == c2
consequentValueMatch _ _ = True

matchConsequent :: Consequent -> Consequent -> Bool
matchConsequent (Consequent cName1 cs1) (Consequent cName2 cs2) =
  cName1 == cName2 && and (zipWith consequentValueMatch cs1 cs2)
  
--findMatches :: Consequent -> KnowledgeBase -> [Consequent]
--findMatches c (KnowledgeBase assertions consequents) =
--  map assertionToConsequent (filter (matchAssertion c) assertions) ++
--  (filter (matchConsequent c) consequents)

