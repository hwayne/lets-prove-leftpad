# [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html)

Note that I'm an absolute novice at using TLAPS, and I used this as an
exercise to practice using it. The proof is absurdly long, but it
has the virtue of having been mechanically checked.

## About TLAPS

THe TLA+ Proof System (TLAPS) is a mechanical proof checker for proofs written
in TLA+.

## About the Proof

The leftpad implementation (in PlusCal) is a direct copy of the implementation from the
Dafny solution.

The proof uses an inductive invariant, which is the method advocated by Leslie
Lamport. The overall approach looks like this:


```
THEOREM Spec=>[]Correct
<1>1. Init => Inv
<1>2. Inv /\ [Next]_vars => Inv'
<1>3. Inv => Correct
<1>4. QED
    BY <1>1, <1>2, <1>3
```


where `Inv` is the inductive invariant and `Correct` is the property you want
to prove.


