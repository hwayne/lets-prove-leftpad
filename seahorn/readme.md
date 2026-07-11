# [SeaHorn](https://seahorn.github.io/)

## About SeaHorn

SeaHorn is an automated verification framework for LLVM-based
languages. It takes a C program with assertions, compiles it to LLVM
bitcode, translates the bitcode into Constrained Horn Clauses (CHCs),
and hands those to the [Spacer](https://spacer.bitbucket.io/) solver
built into Z3. Spacer searches for an inductive invariant that proves
every assertion, or for a concrete execution that violates one.

The proof here, `leftpad.c`, contains no loop invariants, lemmas, or
proof hints, only the implementation and the specification (as
assertions); the invariants needed to prove the loops correct are
inferred by the solver. The
[Dafny](../dafny/Leftpad.dfy) and [Frama-C](../frama-c/leftpad.c)
proofs verify similar imperative code but annotate their loops with
explicit invariants; the [smtlib](../smtlib/leftpad.smt) and
[z3py](../z3py/leftpad.py) proofs are equally automatic but prove a
declarative definition of leftpad rather than loop code. The trade-off
for the automation is less control: if the solver diverges, you cannot
supply the missing invariant annotation; you have to reshape the
problem instead.

## About the proof

The code under verification is an ordinary imperative `leftpad`: two
loops writing into an output buffer. The proof lives in `main`, a
verification harness in which every input (the pad character, the
target length, the string contents and its length) is nondeterministic,
so proving the assertions proves them for all inputs. There are no
upper bounds on the string length or the padding.

The three properties of leftpad are checked as follows:

1. The length of the output is `max(n, len(str))`: asserted directly
   on the length returned by `leftpad`.

2 & 3. The prefix is all padding and the suffix is the original
   string. These properties are universally quantified over every
   position of the output. Instead of a quantified assertion, the
   harness picks a
   single symbolic index `j`, constrained only to be non-negative, and
   asserts the property at `out[j]` whenever `j` falls inside the
   output. Since `j` is arbitrary, SeaHorn must prove the assertion
   for every value of `j`, which is the universally quantified
   property. This keeps the invariants Spacer needs quantifier-free.

The only assumption on the inputs is `len >= 0`, which says the input
string has a non-negative length.

One caveat: SeaHorn's default encoding models signed integer
arithmetic as exact mathematical arithmetic, so this proof does not
account for overflow of `n - len`.

## Running it

With [Docker](https://hub.docker.com/r/seahorn/seahorn-llvm14):

```
docker run -v $(pwd):/host -it seahorn/seahorn-llvm14:nightly \
    sea pf /host/leftpad.c
```

SeaHorn prints `unsat`, meaning the verification conditions are
unsatisfiable: no execution of `leftpad` can violate the specification.

## About me

I'm [John Lu](https://johnlyu2.github.io/), a PhD student at
UWaterloo. My research interests are at the intersection of formal
methods and machine learning.
