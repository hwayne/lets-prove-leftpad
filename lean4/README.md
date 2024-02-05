# Lean 4 leftpad

This is a port of the `leftpad` function and correctness proofs from the
now deprecated Lean version 3 to the [Lean 4](https://lean-lang.org/)
theorem prover.


## About Lean 4

Lean 4 is a Dependently-Typed Programming Language designed for verified
programming, featuring efficient run-time system (with multithreading), flexible
macro system (with syntactic extensions and elaborator reflections) and some
advanced type system elements (quotient types, mutual and nested inductive
types, etc.). Thanks to strict separation of total and non-total functions,
as well as great interactive development support via VS Code and Emacs plugins,
Lean 4 also excels as a Proof Assistant to formalizing mathematics as evidenced
by the [Mathlib](https://github.com/leanprover-community/mathlib4) project.


## About the Code

All the code is in [`leftpad.lean`](./leftpad.lean) file. It's split into two
sections.

The first part is a literal port of the `leftpad` function from the
Lean 3 [code](../leanprover/leftpad.lean), it's defined in terms of lists of
arbitrary elements (not necessarily characters).

The second part in the `Strings` namespace defines another version of `leftpad`
operating on `String`s (which are internally UTF8 strings in Lean 4).


## About the Proofs

The proofs a fairly verbose due to two reasons: the major one being me doing
them in a pretty straightforward and not very smart way, while another one
is that I only used built-in Lean 4 library, which intentionally very minimal,
which lead me to prove a number of auxiliary lemmas stating basic properties of
operations involved in the `leftpad` function and correctness conditions.

For the proofs (even the statements) of `leftpad_prefix` and `leftpad_suffix`
for `String`s I kinda cheat and reduce them to the statements on `List Char`
instead, reusing some lemmas developed for the original `leftpad` proofs.


## About me

I'm Alex Chichigin ([Github](https://github.com/gabriel-fallen/),
[blog](https://dev.to/gabrielfallen)) a formal methods enthusiast. :)
