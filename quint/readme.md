# [Quint](https://quint-lang.org/)

Quint is a specification language for writing executable state-machine models
and properties. Quint specifications can be simulated with `quint run` or
`quint test`, and checked with model checkers. The integrated checker used here
is [Apalache](https://apalache-mc.org/), which translates Quint verification
conditions to SMT.

## About Quint

Quint looks a lot like a cleaned-up, executable dialect of TLA+. A model has
state variables, an `init` action, and a `step` action. An action describes a
relation between the current state and the next state, using primed variables
such as `output'`.

Quint has ordinary executable tests, but the proof below is not just a test.
The `verify` command asks Apalache to prove an inductive invariant:

1. The invariant holds in every initial state.
2. If it holds before a step, it holds after the step.
3. The invariant implies the desired correctness property.

This is the same proof shape as the TLA+/TLAPS proof, but the proof obligations
are discharged automatically by Apalache instead of written as a structured
TLAPS proof.

## About the Proof

This version models leftpad as a small transition system:

1. Choose an arbitrary padding character `c`, target length `n`, and input
   string `s`.
2. Start with `output = s` and `i = 0`.
3. Compute `pad = max(n - s.length(), 0)`.
4. While `i < pad`, prepend `c` to `output` and increment `i`.

Quint does not have a dedicated character type, so this proof represents a
character as a record `{ code: int }`. The set of possible characters is
`CHARS = Int.map(i => { code: i })`, so the proof ranges over infinitely many
character values and over all finite lists of those characters.

The key inductive invariant is `loopInv`. It says:

1. The variables have the expected domains: `n` and `i` are natural numbers,
   `c` is a character, and `s` and `output` are finite character lists.
2. `output.length() == s.length() + i`.
3. The first `i` elements of `output` are the padding character.
4. The original input `s` appears after those `i` padding elements.

The checked correctness property is `correct`. When the loop is done, it proves
the three leftpad requirements:

1. The output length is `max(n, s.length())`.
2. The prefix contains padding characters and nothing but padding characters.
3. The suffix is the original input list.

## Checking the Proof

To run one executable example:

```sh
quint test quint/leftpad.qnt --main leftpadExamples --match leftpadFive
```

To check the proof:

```sh
quint typecheck quint/leftpad.qnt
quint verify quint/leftpad.qnt --inductive-invariant loopInv --invariant correct
```

The proof command checks the inductive-invariant obligations.
