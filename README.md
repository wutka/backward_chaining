# Backchain - Backward-chaining Rule Evaluator

This is a simple assertion & rule evaluator that uses
backward chaining to attempt to prove a rule. The
format of an assertion is:
```
name value1 value2 value3 ... valueN
```
A value can just be a symbol (A-Z, a-z, 0-9, - and \_) or it can
be a quoted string with \\" used to embed a quote within a string.
For example
```
is-parent Fred "Billy Ray"
```

A rule has the form:
```
assertion :- consequent1, consequent2, ... consequentN
```
Although you can specify multiple consequents, you'll probably
have one for most rules.
An assertion can be a simple expression that looks like an assertion
except that in addition to symbols and strings it can contain variables
that look like ? followed by a symbol (e.g. ?x or ?foo). You can also
combine assertions with "and", "or", and use optional parentheses.
For example:
```
(is-player ?x) and (is-good ?x) :- highly-paid ?x
```

When you run the program, it loads the data.txt file by default, and
you can either immediately start entering queries (e.g. assertions)
that it will either prove as true or false, or you can use any
of the following commands:

```
:a    -  List assertions
:r    -  List rules
+a    -  Start adding new assertions (blank line when done)
+r    -  Start adding new rules (blank line when done)
-an   -  Delete assertion n (numbered starting at 1)
-rn   -  Delete rule n (numbered starting at 1)
:save -  Save to file (system will prompt for filename)
:load -  Load from file (system will prompt for filename)
:new  -  Start with new empty knowledge base
:quit -  Quit
:help -  Display help information
```

