# [Maude](http://maude.cs.illinois.edu/)

"Maude is a high-performance reflective language and system supporting both equational and rewriting logic specification and programming for a wide range of applications." ([Maude Overview](http://maude.cs.illinois.edu/w/index.php/Maude_Overview))

## About Maude

Maude is a programming language which has good support for specifying and verifying concurrent/nondeterministic systems, and also offers many convenient features not found in most programming languages, such as true support for "rewriting modulo axioms" such as commutativity and associativity (we use the latter in our definition of strings).
There are several provers and checkers available in Maude, such as the [Inductive Theorem Prover](http://maude.cs.uiuc.edu/tools/itp/) (ITP), which we use here, the [Maude Termination Tool](http://maude.cs.illinois.edu/tools/mta/), the [Rewriting Logic Tool](http://maude.cs.illinois.edu/tools/rltool/) (RLTool), currently being worked on, which is useful for proving properties of programs specified in generic rewriting logic, as well as [many others](https://github.com/maude-team/MFE).
It has also heavily influenced the [K Framework](https://github.com/kframework/k), a tool for formally specifying programming languages, which generates interpreters, verifiers, model checkers, and other similar tools given the specification of a programming language.

## About the Proof

We represent strings as lists of characters (Maude's built-in string type doesn't work well with induction), and use a very straightforward implementation of `leftpad`.
Most of the auxiliary functions are reimplemented in this file because we're not using the standard library, as mentioned.
```
op leftpad : Nat Nat Str -> Str .
eq leftpad(N, C, S) = repeat(N - length(S), C) S .
```

We use Maude's [Inductive Theorem Prover](http://maude.cs.uiuc.edu/tools/itp/) (ITP) to do the proof, proving the three correctness properties and a couple of smaller lemmas about the various functions.
First, the length constraint.
Note that `goal len : LEFTPAD |- ...` means that we've introduced a new goal, which is to prove that the RHS of the turnstile is true in the `LEFTPAD` module; `A{N:Nat}` means "forall natural numbers `N`".
The rest is fairly standard.
```
(goal len : LEFTPAD
    |- A{N:Nat ; C:Nat ; S:Str}
        ((length(leftpad(N, C, S))) = (maximum(N, length(S)))) .)
```

Here we check that the prefix is all padding by reusing the repeat function.
```
(goal prefix : LEFTPAD
    |- A{N:Nat ; C:Nat ; S:Str}
        ((take(N - length(S), leftpad(N, C, S))) = (repeat(N - length(S), C))) .)
```

And finally, we check that the
```
(goal suffix : LEFTPAD
    |- A{N:Nat ; C:Nat ; S:Str}
        ((drop(N - length(S), leftpad(N, C, S))) = (S)) .)
```

Notes on the actual proof commands: `ind` means "induction", `ind*` means "induction, then `auto`", `cns` performs universal quantifier elimination (I believe it stands for "Constant Name Subsitution").

## About Me

My name is [Reed Oei](http://reedoei.com/), I'm a student at [the University of Illinois at Urbana-Champaign](https://cs.illinois.edu/) studying Math and CS.
I'm interested in Theorem Provers/Proof Assistants, Programming Languages and Formal Methods.

