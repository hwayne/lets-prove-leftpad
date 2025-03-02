# [Creusot](https://github.com/xldenis/creusot)

## About Creusot

Creusot is one of the most mature tools of deductive verification for Rust. It uses Why3 as
a backend.

## About the proof

The version of Creusot that was used few years ago in this proof was a striking example of
*research software.* The current version is much more mature.

To verify this code:

1. Install Rust Nightly and Creusot
2. Replace `{path_to_creusot}` in `Cargo.toml` with the path to Creusot
3. Run `cargo creusot prove`

There's still a lot of `@` in the spec, but now it's postfix and some of them are no longer necessary.
A noticeable improvement in readability!

A few `#[invariant(inv(r))]` are necessary because of [creusot#1122](https://github.com/creusot-rs/creusot/issues/1122).

The first postcondition ensures length, the second ensures the prefix full of `c` and the last
precondition ensures that values in the tail correspond to the values of the original slice.

The code style is deliberatly different from the standard Rust style. It favours tersness and
consistent usage of spaces for accent. Nonetheless, obscure macros in the style of
[ngn/k](https://codeberg.org/ngn/k) are avoided to make reading the code more confortable
for people unfamiliar with array programming.

## About the author

A random dude on the internet, who teached himself a bit of Hoare logic to be qualified enough
to say that (total and dependently typed) functional programming is easier to analyze
because of purity (and so many other reasons beyond purity).
