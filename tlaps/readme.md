# [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html)

Note that I'm an absolute novice at using TLAPS, and I used this as an
exercise to practice using it.

The proof as writen is absurdly long. No doubt a more experienced program
prover would have written a simpler proof, and I made no effort to simplify it
once it was complete. However, it has the virtue of being mechanically checked.

## About TLAPS

THe TLA+ Proof System (TLAPS) is a mechanical proof checker for proofs written
in TLA+.

## About the Proof

The leftpad implementation (in PlusCal) is a direct copy of the implementation from the
implementation used in the Dafny solution. (I didn't look at the Dafny proof,
though).

The proof uses an inductive invariant, which is the proof method advocated by Leslie
Lamport. The overall approach for proof by inductive invariant looks like this:


```
THEOREM Spec=>[]Correct
<1>1. Init => Inv
<1>2. Inv /\ [Next]_vars => Inv'
<1>3. Inv => Correct
<1>4. QED
    BY <1>1, <1>2, <1>3
```

where `Inv` is the inductive invariant and `Correct` is the property you want
to prove. In this case, that property is the leftpad specification.

## The inductive invariant

The inductive invariant looks like this:

```
Inv == /\ TypeOK
       /\ \E prefix \in Seq({c}) : output = prefix \o s
       /\ Len(output) = Len(s) \/ Len(output) <= n
       /\ Len(output) = Len(s) + i 
       /\ pad = max(n - Len(s), 0)
       /\ i>=0
       /\ Correct
```

where `TypeOK` asserts the correct type of the variables, and `Correct` is the
correctness condition for leftpad.

I came up with the invariant by starting with `Inv = TypeOK /\ Correct` and
using TLC to check if `Inv` was, indeed, an inductive invariant. When a
counterexample was found, I added another conjunction to tighten it up.

To check the inductive invariant, I set up the following TLC model:

```
Temporal formula: ISpec
What is the model?
    alphabet <- {"a", "b"}
Invariants: Correct
Definition Override:
    Nat <- 0..3
    Seq(S) <- UNION {[1..m -> S] : m \in Nat}
```

In general, checking an inductive invariant is hard because the state space can
be enormous. Lamport describes a strategy for using pseudo-random sampling of
the state space in [Using TLC to Check Inductive Invariance](https://lamport.azurewebsites.net/tla/inductive-invariant.pdf),
but I didn't need it in this case.
