# Prolog

Prolog is a logic programming language. It is based on First Order Logic and features unification and non-determinism.

A Prolog program is made of predicates. Each predicate can be one or more clauses, and each clause can be a rule or a fact. For a predicate to be true, at least one of the clauses must be true. A fact is true by itself, and a rule is true iff the body of the rule is true.

The program itself it's a transcription of the spec to Prolog code. Note that we should not give
an imperative meaning to the rules but it can help in case of performance.

In this case, it shows that in logic programming, the code itself is the proof, as the solution was built using the assertions of the given problem and not a procedure on how to build the solution.

To run it, use [Scryer Prolog](https://www.scryer.pl), load the file and execute some tests:

```
scryer-prolog leftpad.pl
?- leftpad(!, 5, "foo", Ls).
   Ls = "!!foo"
;  false.
?- leftpad(!, 2, "foo", Ls).
   Ls = "foo"
;  false.
```
