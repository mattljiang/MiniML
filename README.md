# MiniML
MiniML is an interpreter for a simple programming language based on a mini subset of OCaml, and is written in OCaml. 

## Some Background
When creating a programming language, one must define what expressions make up the language, as well as what happens when a user writes code using those expressions and runs their program. That is, how those expressions are evaluated to return a value (e.g. how "(fun x -> x + x) 12" evaluates to "24"). An interpreter is the implementation of this evaluation process. There are three models of evaluation implemented in this project, representing three different ways to evaluate expressions: the substitution model, the dynamically scoped environment model, and the lexically scoped environment model. In brief, the substitution model works by appropriately substituting variables with their values. The dynamically scoped environment model works by evaluating expressions in an environment that maps variables to their values; this allows for better binding constructs (e.g. “let” and “let rec”) and the potential for imperative programming. The lexically scoped environment model is similar to the previous model. The difference is that it evaluates functions using the lexical environment when they were defined, rather than the dynamic environment when they are called. This is accomplished by implementing closures. 

## Code Structure
*evaluation.ml* contains implementations of three evaluators each using a different model of evaluation. 
*expr.ml* declares types of expressions supported by MiniML as well as functions used in *evaluation.ml*.
*miniml_lex.mll* is a lexical analyzer.
*miniml_parse.mly* is a parser.
*miniml.ml* runs a REPL using the evaluator specified in *evaluation.ml*.

## Attributions
This was a final project option for the class CS51 at Harvard University. As such, some of the modules were provided by the course - namely the lexical analyzer, the parser, and the code used to incorporate those modules. Code in *evaluation.ml* and *expr.ml* to implement the interpreter, the focus of this project, was written by Matt Jiang.


