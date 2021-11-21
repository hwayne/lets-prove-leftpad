# [Dafny](https://github.com/dafny-lang/dafny)

The one that started it all! The leftpad challenge, not the idea of proving. [You can run the leftpad proof here](https://rise4fun.com/Dafny/nbNTl).

## About Dafny

Dafny is an imperative/OOP language with an additional set of _specification constructs_ that you can use to describe the intended behavior of your program. During compilation Dafny will use the SMT solver (usually Z3) to check that your program matches the specification. At runtime, the specification constructs are removed so your code stays performant.

Dafny tries to infer the complete proof, but it usually needs help with intermediate steps. So we interleave our code with functional assertions and invariants to provide intermediate stages for the prover. It might not be able to prove `A => C`, so instead you ask it to prove `A => B` and later `B => C`. This concept of intermediate steps of your proof crops up in almost all verifiers. We'll see how Dafny can do it in the next section.

## About the Proof

Our implementation of leftpad is pretty crude. We start by calculating the amount of padding we need, and count up to the padding number, prepending our string by a padding character each time.

The core of the work happens in `while i < pad`, which is a loop. Loops play a very important role in imperative proofs. Assuming we're not using gotos or recursion, loops are the only place where a program might run infinitely. If we provide a proof that `while` has a finite number of loops, we know our program will always terminate. We do this by having Dafny prove a **loop variant**: that some value decreases on each cycle, and that the loop ends when that value reaches zero. This is `decreases pad - i`.

We also have **loop invariants**, such as `invariant |v| == |s| + i`. Dafny checks that the invariant is true at the start and end of every loop cycle. It can be false in the loop body, but it must be true again by the time the loop finishes. By proving the loop invariants, we can infer what our final state will be when the loop terminates.

One way to think of this is that we have an initial state, a final state, and a set of intermediate computations. By using loop invariants, we can prove that all of our intermediate computations get us closer to our final state having the specification we want. The ability to prove intermediate computations can simplify a lot of otherwise-complicated proofs.

## About Me

Same dude who's running the repo. Hi!
