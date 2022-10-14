# [Creusot](https://github.com/xldenis/creusot)

## About Creusot

Creusot is a deductive verification tool for rust, which uses Why3 as a backend. At the moment
of writing this readme, Creusot is still a *research software*, but there already exist
a nontrivial software verified with it: [CreuSAT](https://github.com/sarsko/creusat).

## About the proof

Since Creusot is a still *research software,* the code has to use nightly Rust, and to verify
it you need a git version of Why3 and Creusot.

To verify it:

1. Install appropriate versions of Rust, Creusot, Why3, and CVC5
2. Run `cargo creusot --span-mode=absolute -- --features=contracts`
3. Run `«creusot repo»/ide target/debug/leftpad-rlib.mlcfg`
4. In Why3 IDE, apply “Split VC” to `leftpad'vc`
5. Apply CVC5 to `split_vc`

Specification is ridden with model taking operator (`@`) because a better way is still an open
question.

The `Model` trait has to be defined, because `creusot-contracts-dummy` does not provide it yet,
and without it code can't be compiled normally. The main reason why `leftpad` parametrizes on
`C:Copy+Model` is because the `char` type has no model yet.

`maxz` is defined because Creusot does not support `x.max(y)` yet. `sub` is defined
because the author did not bother to look how to do saturated negation in Rust, and it is very
likely that it's not supported by Creusot anyway.

Invariants have labels, because invariants without labels are not yet supported.

The first postcondition ensures length, the second ensures prefix full of `c` and the last
one precondition ensures that values in the tail correspond to the values of the original slice.

The code style is deliberatly different from the standard Rust style. It favours tersness and
consistent usage of spaces for accent. Nonetheless, obscure macros in the style of
[ngn/k](https://codeberg.org/ngn/k) are avoided to make reading the code more confortable
for people unfamiliar with array programming.

## About the author

A random dude on the internet, who teached himself a bit of Hoare logic to be qualified enough
to say that (total and dependently typed) functional programming is easier to analyze
because of purity (and so many other reasons beyond purity).
