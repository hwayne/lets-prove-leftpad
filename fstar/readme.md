# [FStar](https://www.fstar-lang.org/)

## About FStar

FStar / F* is a language in the ML / OCaml family, a joint project of INRIA and Microsoft Research. It includes a very sophisticated set of static verification components: a monadic effect system, refinement types, dependent types, and a Dijkstra-style weakest precondition calculus. All these route into (as much as possible) an SMT solver, and many proofs only need to be lightly sketched with the remainder discharged automatically.

Once verified, FStar programs' computational content can be extracted to F# or OCaml for execution. Furthermore a subset of the language called Low* can be extracted to C code, so if you confine your program to the Low* fragment you have a tool for verifying properties of very low level (non-allocating, pointer-manipulating, bit-twiddling) systems code. See the [KreMLin](https://github.com/FStarLang/kremlin) tool for details.

## About the proof

The leftpad proof is conducted entirely automatically by stating a set of correctness properties (the `assert`s in the body of `leftpad_correct`) concerning a separate implementation (`leftpad`) and letting the SMT solver discharge them. No explicit proof terms (tactics, equalities, pre/post conditions, invariants, etc.) appear; it's all implicit in this case. More complex cases require more guidance from the user, though many cases amount to just helping it take an inductive step.

This example proves properties out of line from the implementation, in a separate spec function. This is a matter of style. FStar programs often encode logical properties in a mixture of styles: some refinement types, some pre/post conditions in the monadic effect system, and some out-of-line proofs of additional properties. The styles are complementary, enable a high degree of flexibility in how code is organized, understood, verified and reused.

On my laptop (2013 macbook air), verification takes a little over a second:

```
$ fstar.exe Leftpad.fst
Verified module: Leftpad (1171 milliseconds)
All verification conditions discharged successfully
```

## About me

Just another programmer.