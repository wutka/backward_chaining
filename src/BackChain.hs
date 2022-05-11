module BackChain where

import Data.Either
import Data.Maybe
import Data.List
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

ruleMatch :: Consequent -> Rule -> Bool
ruleMatch c (Rule _ cs) =
  any (matchConsequent c) cs
  
--findMatches :: Consequent -> KnowledgeBase -> [Consequent]
--findMatches c (KnowledgeBase assertions consequents) =
--  map assertionToConsequent (filter (matchAssertion c) assertions) ++
--  (filter (matchConsequent c) consequents)

updateVarMapWithPair :: VarMap -> (RuleValue, RuleValue) -> VarMap
updateVarMapWithPair vm (RuleConstant _, RuleConstant _) = vm
updateVarMapWithPair vm (RuleConstant _, RuleVariable _) = vm
updateVarMapWithPair vm (RuleVariable v, RuleConstant s) =
    Map.insert v s vm
updateVarMapWithPair vm (RuleVariable _, RuleVariable _) = vm

updateVarMap :: VarMap -> Consequent -> Consequent -> VarMap
updateVarMap vm (Consequent _ c1) (Consequent _ c2) = foldl' updateVarMapWithPair vm (zip c1 c2)

applyMapToValue :: VarMap -> RuleValue -> RuleValue
applyMapToValue vm rc@(RuleConstant s) = rc
applyMapToValue vm rv@(RuleVariable v) =
  maybe rv RuleVariable $ Map.lookup v vm

applyMapToConsequent :: Consequent -> VarMap -> Consequent
applyMapToConsequent (Consequent name v) vm = Consequent name (map (applyMapToValue vm) v)

applyMapToAntecedent :: Antecedent -> VarMap -> Antecedent
applyMapToAntecedent (SimpleExpr name v) vm = SimpleExpr name (map (applyMapToValue vm) v)
applyMapToAntecedent (AndExpr a1 a2) vm = AndExpr (applyMapToAntecedent a1 vm)
                                                  (applyMapToAntecedent a2 vm)
applyMapToAntecedent (OrExpr a1 a2) vm = OrExpr (applyMapToAntecedent a1 vm)
                                                (applyMapToAntecedent a2 vm)
                                         

proveAntecedent :: KnowledgeBase -> Antecedent -> VarMap ->  [VarMap]
proveAntecedent kb (SimpleExpr name v) vm =
  proveConsequent kb (Consequent name v) vm
  
proveAntecedent kb (AndExpr a1 a2) vm =
  foldl' (++) [] (map (proveAntecedentAnd2 kb a2) a1Result)
  where
    a1Result = proveAntecedent kb a1 vm
proveAntecedent kb (OrExpr a1 a2) vm =
  proveAntecedent kb a1 vm ++ proveAntecedent kb a2 vm

proveAntecedentAnd2 :: KnowledgeBase -> Antecedent -> VarMap -> [VarMap]
proveAntecedentAnd2 kb a2 vm =
  proveAntecedent kb (applyMapToAntecedent a2 vm) vm
  
    
proveRule :: KnowledgeBase -> Rule -> VarMap -> [VarMap]
proveRule kb (Rule antecedent _) varMap =
  proveAntecedent kb (applyMapToAntecedent antecedent varMap) varMap
  

proveRuleWithConsequent :: KnowledgeBase -> Consequent -> Consequent -> Rule -> VarMap -> [VarMap]
proveRuleWithConsequent kb ic c rule vm =
  map updateIncomingMap (proveRule kb rule (updateVarMap Map.empty c ic))
  where
    updateIncomingMap inVm = updateVarMap vm (applyMapToConsequent c inVm) ic
                             
proveRuleWithConsequents :: KnowledgeBase -> Consequent -> Rule -> VarMap -> [VarMap]
proveRuleWithConsequents kb ic rule@(Rule _ cs) vm =
  foldl' (++) [] (map proveForConsequent (filter (matchConsequent ic) cs))
  where
    proveForConsequent pc = proveRuleWithConsequent kb ic pc rule vm
    
proveConsequent :: KnowledgeBase -> Consequent -> VarMap -> [VarMap]
proveConsequent kb@(KnowledgeBase assertions rules) c vm =
  assertionMaps ++ consequentMaps
  where
    matchingAntecedents = filter (matchAssertion c) assertions
    assertionsAsConsequents = map assertionToConsequent matchingAntecedents
    assertionMaps = map (updateVarMap Map.empty c) assertionsAsConsequents
    matchingRules = filter (ruleMatch c) rules
    consequentMaps = foldl' (++) [] (map proveEachRule matchingRules)
    proveEachRule r = proveRuleWithConsequents kb c r vm
    
    
    


