module BackChain where

import Lexer
import Data.Either
import Data.Maybe
import Data.List
import qualified Data.Map as Map

-- A value in a rule can be a constant of a variable
data RuleValue =
    RuleConstant String
  | RuleVariable String
  deriving (Eq)

instance Show RuleValue where
  show (RuleConstant c) = showSymbol c
  show (RuleVariable v) = "?"++v
  
-- An assertion has a name and a list of constant values
data Assertion =
  Assertion String [String]
  deriving (Eq)

instance Show Assertion where
  show (Assertion name constants) =
    name ++ " " ++ unwords (map showSymbol constants) ++ "."

-- An antecedent can be a simple named expression, an
-- And expression with two antecedents, or an Or expression
-- with two antecedents
data Antecedent =
    SimpleExpr String [RuleValue]
  | AndExpr Antecedent Antecedent
  | OrExpr Antecedent Antecedent
  deriving (Eq)

instance Show Antecedent where
  show (SimpleExpr name values) =
    name ++ " " ++ unwords (map show values)
  show (AndExpr a1 a2) =
    "(" ++ show a1 ++ ") and (" ++ show a2 ++ ")"
  show (OrExpr a1 a2) =
    "(" ++ show a1 ++ ") or (" ++ show a2 ++ ")"
    
-- A consequent has a name and a list of values
data Consequent =
    Consequent String [RuleValue]
  deriving (Eq)

instance Show Consequent where
  show (Consequent name values) =
    name ++ " " ++ unwords (map show values)
    
-- A rule has an antecedent and a list of consequents
data Rule =
    Rule Antecedent [Consequent]
  deriving (Eq)

instance Show Rule where
  show (Rule antecedent consequents) =
    show antecedent ++ " :- " ++ intercalate ", " (map show consequents) ++ "."

-- The knowledge base contains all the known assertions and rules
data KnowledgeBase =
    KnowledgeBase [Assertion] [Rule]
  deriving (Show, Eq)

-- VarMap is used to map variable names to values
type VarMap = Map.Map String String

data SearchContext =
  SearchContext VarMap [Consequent]
  deriving (Show, Eq)

isConstantValue :: RuleValue -> Bool
isConstantValue (RuleConstant _) = True
isConstantValue _ = False

isConstantConsequent :: Consequent -> Bool
isConstantConsequent (Consequent _ vs) = all isConstantValue vs

-- It is handy to convert an assertion into a consequent (with no
-- variables) so the same matching algorithms can be used
assertionToConsequent :: Assertion -> Consequent
assertionToConsequent (Assertion name vs) =
  Consequent name (map RuleConstant vs)

-- If a rule contains a variable, it matches an assertion value
-- automatically. Otherwise, they only match if the assertion
-- value and the rule value are the same constant
assertionValueMatch :: String -> RuleValue -> Bool
assertionValueMatch s (RuleConstant s2) = s == s2
assertionValueMatch _ (RuleVariable _) = True

-- Returns true if a consequent matches an assertion
matchAssertion :: Consequent -> Assertion -> Bool
matchAssertion (Consequent cName cs) (Assertion aName as) =
  -- Make sure the names match, and then make sure all values match
  aName == cName && and (zipWith assertionValueMatch as cs)

-- For two consequent values to match, if either consequent contains
-- a variable, they match, otherwise, if they are both constants,
-- the constants have to match
consequentValueMatch :: RuleValue -> RuleValue -> Bool
consequentValueMatch (RuleConstant c1) (RuleConstant c2) = c1 == c2
consequentValueMatch _ _ = True

-- Returns true if two consequents have the same name and they
-- match in places where they each have a constant
matchConsequent :: Consequent -> Consequent -> Bool
matchConsequent (Consequent cName1 cs1) (Consequent cName2 cs2) =
  cName1 == cName2 && and (zipWith consequentValueMatch cs1 cs2)

-- A consequent matches a rule if it matches any of the rule's consequents
ruleMatch :: Consequent -> Rule -> Bool
ruleMatch c (Rule _ cs) =
  any (matchConsequent c) cs

-- Given a map and two rule values, if the first value is a variable
-- and the second value is a constant, update the map to map the
-- variable to the constant value
updateVarMapWithPair :: (RuleValue, RuleValue) -> VarMap -> VarMap
updateVarMapWithPair (RuleConstant _, RuleConstant _) vm = vm
updateVarMapWithPair (RuleConstant _, RuleVariable _) vm = vm
updateVarMapWithPair (RuleVariable v, RuleConstant s) vm =
    Map.insert v s vm
updateVarMapWithPair (RuleVariable _, RuleVariable _) vm = vm

-- Compare two consequents and for all the variables in the first one
-- where the corresponding value in the second consequent is a constant,
-- update the map to map the variable to that constant value
updateVarMap :: VarMap -> Consequent -> Consequent -> VarMap
updateVarMap vm (Consequent _ c1) (Consequent _ c2) = foldr updateVarMapWithPair vm (zip c1 c2)

-- If a value is a variable, see if it is in the map, and if so, replace
-- it with a constant, otherwise leave the variable intact
applyMapToValue :: VarMap -> RuleValue -> RuleValue
applyMapToValue vm rc@(RuleConstant s) = rc
applyMapToValue vm rv@(RuleVariable v) =
  maybe rv RuleConstant $ Map.lookup v vm

-- Replace any variables in a consequent that have mappings in
-- the variable map
applyMapToConsequent :: Consequent -> VarMap -> Consequent
applyMapToConsequent (Consequent name v) vm = Consequent name (map (applyMapToValue vm) v)

applyMapToAntecedent :: Antecedent -> VarMap -> Antecedent
applyMapToAntecedent (SimpleExpr name v) vm = SimpleExpr name (map (applyMapToValue vm) v)
applyMapToAntecedent (AndExpr a1 a2) vm = AndExpr (applyMapToAntecedent a1 vm)
                                                  (applyMapToAntecedent a2 vm)
applyMapToAntecedent (OrExpr a1 a2) vm = OrExpr (applyMapToAntecedent a1 vm)
                                                (applyMapToAntecedent a2 vm)
                                         
-- Attempts to prove an antecedent by examining the knowledge base
proveAntecedent :: KnowledgeBase -> Antecedent -> SearchContext ->  [SearchContext]

-- If the antecedent is a simple expression, convert it to a consequent
-- and then attempt to prove the consequent against the knowledge base
proveAntecedent kb (SimpleExpr name v) sc =
  proveConsequent kb (Consequent name v) sc

-- If the antecedent is an AndExpr, first prove the left antecedent. This
-- will result in a list of variable mappings. For each of these mappings,
-- apply the mapping to the second antecedent, and then try to prove
-- the second antecedent.
-- For example, given the antecedent is-foo ?x and is-bar ?y and
-- two matching assertions  is-foo "baz" and is-foo "quux", there
-- would be two maps returned in proving the first assertion, one mapping
-- ?x to "baz" and one mapping ?x to "quux". Then, this function will
-- look for all results for is-bar "baz" and then for is-bar "quux".
proveAntecedent kb (AndExpr a1 a2) sc =
  concatMap (proveAntecedentAnd2 kb a2) a1Result
  where
    a1Result = proveAntecedent kb a1 sc

-- Unlike the AndExpr, for the OrExpr we just get all the matches for
-- the left antecedent and all the matches for the right antecedent
-- and don't need to update the right with results from the left.
proveAntecedent kb (OrExpr a1 a2) sc =
  proveAntecedent kb a1 sc ++ proveAntecedent kb a2 sc

-- Apply the incoming map to the second antecedent and try to
-- prove the second antecedent
proveAntecedentAnd2 :: KnowledgeBase -> Antecedent -> SearchContext -> [SearchContext]
proveAntecedentAnd2 kb a2 sc@(SearchContext vm _) =
  proveAntecedent kb (applyMapToAntecedent a2 vm) sc
  
-- To prove a rule given a particular variable map, apply the map
-- to the antecedent and then try to prove the antecedent
proveRule :: KnowledgeBase -> Rule -> SearchContext -> [SearchContext]
proveRule kb rule@(Rule antecedent _) sc@(SearchContext varMap _) =
  proveAntecedent kb (applyMapToAntecedent antecedent varMap) sc
  
-- To prove a rule by matching against a specific consequent in the rule,
-- initialize a variable mapping in which any variables in the rule's consequent
-- are mapped to any constants in the incoming consequent. The variables
-- in the incoming consequent are left alone until after proving the rule.
-- When the rule is proven, it returns a list of variable mappings. For
-- each of these mappings, we apply them to the rule's consequent, which
-- should replace all variables with constants, and then we update the
-- incoming variable mapping, by matching the rule's consequent, which
-- should now have all constants, against the incoming consequent to see
-- if there are any variables that can be bound.
-- For example, given an incoming consequent is-foo ?x and a rule that
-- has a consequent is-foo ?y, after the rule is proven, we get back a list
-- of mappings, each of which should have a value for the ?y variable.
-- For example, suppose there are two maps, one mapping ?y to "bar" and
-- another mapping it to "baz".
-- We apply ?y="bar" to is-foo ?y to get is-foo "bar", and then match
-- is-foo "bar" against the incoming consequent "is-foo ?x", to update
-- the incoming map to have ?x="bar" after comparing the two consequents,
-- and then do the same again for the ?y="bar" mapping, so the result
-- is a list of two maps, one containing ?x="bar" and the other containing
-- ?x="baz" (there may be additional variables in the maps that were
-- in the incoming var map
proveRuleWithConsequent :: KnowledgeBase -> Consequent -> Consequent -> Rule -> SearchContext -> [SearchContext]
proveRuleWithConsequent kb ic c rule sc@(SearchContext vm csqs) =
  map (updateIncomingContext ic vm c) (proveRule kb rule (SearchContext (updateVarMap Map.empty c ic) csqs))

updateIncomingContext :: Consequent -> VarMap -> Consequent -> SearchContext -> SearchContext
updateIncomingContext ic vm c (SearchContext invm csqs) =
  SearchContext updatedMap csqs
  where
    resultingConsequent = applyMapToConsequent c invm
    updatedMap = updateVarMap vm resultingConsequent ic
    updatedConsequent = applyMapToConsequent ic updatedMap
  
-- To prove a rule for an incoming consequent, we look for all the consequents
-- in the rule that match it. For example, if an incoming consequent is is-foo "bar"
-- and the rule has two consequents  is-foo ?x and is-foo ?y, we try each of
-- them. We then concatenate the var map lists returned in each proveForConsequent
-- call to make one list of maps.
proveRuleWithConsequents :: KnowledgeBase -> Consequent -> Rule -> SearchContext -> [SearchContext]
proveRuleWithConsequents kb ic rule@(Rule _ cs) sc@(SearchContext vm csqs) =
  concatMap proveForConsequent (filter (matchConsequent ic) cs)
  where
    proveForConsequent pc = proveRuleWithConsequent kb ic pc rule sc

-- To prove a consequent, see if it matches any assertions, and then see if it
-- matches any rules. In order to support backtracking, rather than stopping
-- at the first match, we return a variable mapping for each possible match.
proveConsequent :: KnowledgeBase -> Consequent -> SearchContext -> [SearchContext]
proveConsequent kb@(KnowledgeBase assertions rules) c sc@(SearchContext vm csqs) =
-- If we have already searched for this consequent, return the current context
  if elem c csqs then
    [sc]
  else
    assertionMaps ++ consequentMaps
  where
    -- If this consequent is a constant, flag that we have searched for it
    newCsqs = if isConstantConsequent c then c:csqs else csqs
    -- Find all the assertions that match the consequent
    matchingAssertions = filter (matchAssertion c) assertions
    -- Convert the matches assertions to consequents
    assertionsAsConsequents = map assertionToConsequent matchingAssertions
    -- Create variable mappings by matching constants in the assertion
    -- against variables in the consequent
    assertionMaps = map (updateContext c) assertionsAsConsequents
    -- update the context with a new map
    updateContext c ac = SearchContext (updateVarMap Map.empty c ac) newCsqs
    -- Look for all rules that have a consequent that matches the consequent
    matchingRules = filter (ruleMatch c) rules
    -- Create the list of variable maps resulting from proving the rule
    -- from the given consequent
    consequentMaps = concatMap proveEachRule matchingRules
    -- Try proving the rule from the given consequent
    proveEachRule r = proveRuleWithConsequents kb c r (SearchContext vm newCsqs)
    
    
    


