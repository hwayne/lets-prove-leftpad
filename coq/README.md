# leftpad: A Solution in Coq

This Coq solution to the leftpad challenge takes a functional-programming
approach to implementing the algorithm, and proves the correctness as a
theorem separate from the implementation.

As such it differs from an imperative-programming approach, where arrays of
characters are modified, and differs from a functional,
dependently-typed-programming approach, where the implementation's type
constrains its implementation and never compiles without meeting that
specification.

## The Functional-Programming Approach

A functional programmer, faced with a problem like this one, reaches quickly
for some *combinators* that can be used to solve the problem without any loops,
without any loop indexes, and in a more-or-less "obviously correct" way. In
this case, we implement leftpad as "calculate the correct number of pad
characters, and append them on the left." Such a solution can hardly fail to
be correct!

```coq
Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.
```

However, we can't ignore "loops" forever. Some of the functions that we use in
the implementation--and in the specification--are recursive, and proving
things about them usually requires induction.

## An Opinion

Our point of view is that proving the correctness of a function like
`leftpad`, which only makes direct use of a few standard library functions,
should be "easy", if only

  * the standard library comes with enough lemmas about its functions,
  * the standard lemmas are easy for the user to find, and interoperable with
    one another, and
  * the proof-search features of the prover are strong enough.

So we honed our solution to the point where it has just one main correctness
lemma that's specific to this problem, and a few definitions that are good
candidates for inclusion in the standard library.

Early attempts showed a struggle between a lemma-base that was very general,
but made proving our theorem more difficult, and one that was well-tailored
to this problem, but full of bad candidates for standard-library inclusion.

## An Elegant Solution

We found that the most elegant balance was to devise a function, `cutn`, which
acts like a kind of inverse to `(++)`: it splits the input at a given offset,
into a prefix and suffix (using Coq standards `firstn` and `skipn`). We use it
in the specification, which reads as follows:

```coq
Lemma leftpad_correctness:
  forall padChar n s,
    length (leftpad padChar n s) = max n (length s) /\
    exists m,
      let (prefix, suffix) := cutn _ m (leftpad padChar n s) in
      allEqual _ prefix padChar /\
      suffix = s.
```

The use of `cutn` is a natural way to express the specification, which talks
about a prefix and suffix, but additionally, since it is an inverse of the
top function in our implementation `(++)`, it made proving easy.

In the end, we only need this one lemma about `cutn` (that `cutn n` is like an
inverse to `(++)`) and one lemma about the relationship of `max` to
plus/minus. Early attempts used lemmas that described slightly more
complicated interactions between `(++)` and the pair of functions, `firstn`,
`skipn`. In general, looking for inverse pairs of functions seems to be a
valuable technique.

Choosing the right lemma base for the basic functions made the proof mostly
automatic. Note that we chose not to put the `cutn_app` lemma into the `list`
hint database, and that is because it is "dangerous": applying it in the wrong
situation could lead to an unprovable goal, and hence makes proof search
harder than it has to be. We prefer hint databases that are "conservative":
whose lemmas don't guess at possibly-unprovable goals, and thus are almost
certain to be worth applying. Such is the case for the lemma `length_app`,
which says that `length (a ++ b) = length a + length b`. However, if we
included `cutn_app`, our proof script could be almost completely naive.

## Afterword

Throughout the world of machine-assisted theorem proving, it seems that the
cultivation of a very well-defined, recombinatory library of lemmas is
essential to having short proofs as well as automatable proofs. The `leftpad`
challenge was no exception.
