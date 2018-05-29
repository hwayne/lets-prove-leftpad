
# Lean

## About Lean

From http://leanprover.github.io/:

> Lean is an open source theorem prover and programming language being
> developed at [Microsoft
> Research](http://research.microsoft.com/). Lean aims to bridge the
> gap between interactive and automated theorem proving, by situating
> automated tools and methods in a framework that supports user
> interaction and the construction of fully specified axiomatic
> proofs. The mathematical components library mathlib for Lean is
> being developed at [Carnegie Mellon
> University](http://www.cmu.edu/).

> The Lean project was launched by Leonardo de Moura at Microsoft
> Research in 2013. It is an open source project, hosted on GitHub.

> You can experiment with an online version of Lean that runs in your
> browser, or try the [online](https://leanprover.github.io/live/)
> tutorials listed under documentation.

Additionally, Lean's logic is based on dependent type theory. Its
proof can be written in term mode, with some syntax
borrowed from Isabelle (e.g. `have`, `show`, `assume`), or in tactics
mode. Contrarily to Coq, tactics are written in Lean itself. With its
extensive use of type classes in the libraries, both the core and
mathlib, and pattern matching borrowed from Idris, this makes writing
Lean specifications, Lean proofs and proof
automation reminiscent of using Haskell.

## Checking the proof

Install Elan, the Lean build tool:

```
curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh
```

In the directory of `leftpad.lean`, call:

```
leanpkg build
```

It will install Lean 3.4.1 and check the proof.

## About the Left-Pad proof

Coming soon

## About Me

I'm Simon Hudon, I'm a PhD student at YorkU. I work on refinement
techniques for distributed and reactive systems along with Z3 and
Lean-based tools for applying those techniques. My Unit-B method has
been published in [The Unit-B Method — Refinement Guided by Progress
Concerns](https://www.researchgate.net/publication/271826296_The_Unit-B_Method_-_Refinement_Guided_by_Progress_Concerns)

I also work part time at Weever Apps, using Haskell and TLA+ for
building reliable distributed systems.
