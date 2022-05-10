{
module Parser where

import Data.Char
import Lexer
import BackChain

}

%name parser
%tokentype { Token }
%error { parseError }

%left and
%left or

%token
    and  { TokenAnd }
    or   { TokenOr }
    sym  { TokenSymbol $$ }
    str  { TokenString $$ }
    var  { TokenVariable $$ }
    '.'  { TokenPeriod }
    ','  { TokenComma }
    '('  { TokenLParen }
    ')'  { TokenRParen }
    ':-' { TokenImplies }

%%

KnowledgeBase : Rule KnowledgeBase { (Right $1) : $2 }
              | Assertion KnowledgeBase { (Left $1) : $2 }
              | { [] }

StrOrSyms : sym StrOrSyms { $1 : $2 }
          | str StrOrSyms { $1 : $2 }
          | { [] }

Assertion : sym StrOrSyms '.' { Assertion $1 $2 }

StrOrSymsOrVars : sym StrOrSymsOrVars { (RuleConstant $1) : $2 }
                | str StrOrSymsOrVars { (RuleConstant $1) : $2 }
                | var StrOrSymsOrVars { (RuleVariable $1) : $2 }
                | { [] }

SimpleExpr : sym StrOrSymsOrVars { SimpleExpr $1 $2 }

AndExpr : Expr and Expr { AndExpr $1 $3 }

OrExpr : Expr or Expr { OrExpr $1 $3 }

Expr  : '(' Expr ')' { $2 }
      | AndExpr { $1 }
      | OrExpr { $1 }
      | SimpleExpr { $1 }

Consequent : sym StrOrSymsOrVars { Consequent $1 $2 }

Consequents : Consequent ',' Consequents { $1 : $3 }
            | Consequent { [$1] }

Rule : Expr ':-' Consequents '.' { Rule $1 $3 }


  

