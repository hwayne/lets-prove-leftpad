This Coq solution to the leftPad challenge takes a functional-programming
approach to implementing the algorithm, and proves the correctness as a
theorem separate from the implementation, rather than implementing the
algorithm with a fully-specific type that must be correct from the outset.

A functional programmer, faced with a problem like this one, reaches quickly
for some combinators that can be used to solve the problem without any loops
and in a more-or-less "obviously correct" way. In this case, we write left pad
as "calculate the correct number of pad characters, and append them on the
left." Such a solution can hardly fail to be correct!

Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.

However, we can't ignore loops forever. Some of the functions that we use in
the implementation--and in the specification--are recursive, and proving
things about them usually requires induction.

Our point of view is that proving the correctness of something like this,
which makes direct use of a few standard library functions, should be "easy",
if only

  (*) the standard library comes with enough lemmas about the standard
      functions,
  (*) the standard lemmas are easy to locate and interoperable with one
      another, and
  (*) the proof-search features of the prover are strong enough.

So we honed our solution to the point where it has just one main correctness
theorem, and a few definitions that are good candidates for inclusion in the
standard library.

Early attempts showed a struggle between a lemma-base that was very general,
but made proving our theorem more difficult, and those that were well-tailored
to this problem, but bad candidates for standard-library inclusion.

We found that the most elegant balance was to devise a function, cutn, which
acts like a kind of inverse to (++). We use it in the specification, which reads as follows:

Lemma correctness:
  forall padChar n s,
    length (leftpad padChar n s) = max n (length s) /\
    exists m,
      let (prefix, suffix) := cutn _ m (leftpad padChar n s) in
      allEqual _ prefix padChar /\
      suffix = s.

cutn is obviously a natural way to express the specification, which talks
about a prefix and suffix, but additionally, since it is an inverse of the
top function in our implementation (++), it made proving easy.

Throughout the world of machine-assisted theorem proving, it seems that the
cultivation of a very well-defined, recombinatory library of lemmas is
essential to having short proofs as well as automatable proofs. The leftpad
challenge was no exception.