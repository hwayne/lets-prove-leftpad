# Lean 4 leftpad

This is a port (but not literal) of the `leftpad` function and correctness proofs
from the now deprecated Lean version 3 to the [Lean 4](https://lean-lang.org/)
theorem prover.


## About Lean 4

Lean 4 is a Dependently-Typed Programming Language designed for verified
programming, featuring efficient run-time system (with multithreading), flexible
macro system (with syntactic extensions and elaborator reflection) and some
advanced type system elements (quotient types, mutual and nested inductive
types, etc.). Thanks to strict separation of total and non-total functions,
as well as great interactive development support via VS Code and Emacs plugins,
Lean 4 also excels as a Proof Assistant for formalizing mathematics as evidenced
by the [Mathlib](https://github.com/leanprover-community/mathlib4) project.


## About the Code

There are two versions: [`leftpad_simple.lean`](./leftpad_simple.lean) and
[`leftpad_brief.lean`](./leftpad_brief.lean)

The first version ("simple") is intended as a more educational one, featuring more
basic straightforward proofs and auxiliary lemmas. It's split into two
sections.

The first part is a literal port of the `leftpad` function from the
Lean 3 [code](../leanprover/leftpad.lean), it's defined in terms of lists of
arbitrary elements (not necessarily characters).

The second part in the `Strings` namespace defines another version of `leftpad`
operating on `String`s (which are internally UTF8 strings in Lean 4).

The second file ("brief") showcases more concise definitions and proofs reflecting
more professional use of Lean 4 closer to real-world applications. Actual real-world
examples can be found in great numbers in the aforementioned Mathlib project.


## About me

I'm Alex Chichigin ([Github](https://github.com/gabriel-fallen/),
[blog](https://dev.to/gabrielfallen)) a formal methods enthusiast. :)

The [`leftpad_brief.lean`](./leftpad_brief.lean) was contributed by
[Сухарик](https://github.com/suhr).
