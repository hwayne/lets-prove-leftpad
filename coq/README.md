This Coq solution to the leftPad challenge takes a
functional-programming approach to implementing the algorithm, and
proves the correctness as a theorem separate from the implementation,
rather than implementing the algorithm with a fully-specific type that
must be correct from the outset.

A functional programmer, faced with a problem like this one, reaches
quickly for some combinators that can be used to solve the problem
without any loops and in a more-or-less "obviously correct" way. In
this case, we write left pad as "calculate the correct number of pad
characters, and append them on the left." Such a solution can hardly
fail to be correct!

Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.

However, we can't ignore loops forever. Some of the functions that we use in
the implementation--and in the specification--are recursive, and
proving things about them usually requires induction. The functions
are all part of the standard Coq library, and so it would be
reasonable to expect their correctness propositions to also be part of
the library, along with some useful lemmas about their interaction. As
it happens, the standard library is a little short of those lemmas, so
we prove a few in this project.

We view that the 
The recursive functions we use in the implementation are repeat,
length and append (app, or (++)). In the specification we also use
take, drop, and listall (which asserts that a predicate holds for each
element of a list).

So we state and prove the following lemmas:

  (* Showing the length of a concatenation, and of a "repeat". *)
  app_length
  repeat_length

  (* Showing what happens when you append two lists and then break it
  apart, perhaps at a different places. *)
  
  take_app
  drop_app

  take_repeat

Our take_app/drop_app lemmas have much more power than we need, since
we only expect to break the concatenation apart at the very place
where we put it together in the first place.

Where an imperative programmer reaches for a loop, perhaps even an
index variable, ...

Earlier, we mentioned
Indeed, the Idris solution in this compendium goes so far as to take
this implementation as its spec.

In this Coq solution, we take the specification explictly as three
separate statements to be proven (albeit together in one logical
conjunction).

