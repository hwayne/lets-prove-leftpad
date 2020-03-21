# [Frama-C](https://www.frama-c.com/)

## About Frama-C

From the Frama-C website:

> Frama-C is an extensible and collaborative platform dedicated to source-code analysis of C software.

In other words, Frama-C is a set of tools for analysing C programs.
Most relevant for this example is the Weakest Precondition plugin (`-wp`),
which uses [weakest precondition calculus](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)
to prove [ANSI/ISO C Specification Language](https://en.wikipedia.org/wiki/ANSI/ISO_C_Specification_Language) (ACSL) annotations in C programs.

ACSL is based on the [Java Modeling Language](https://en.wikipedia.org/wiki/Java_Modeling_Language) (JML),
so the annotations are quite similar to the Java example in this repository.

Debian ships with some rather old versions of Frama-C (14.0 Silicon and 16.0 Sulfur vs 20.0 Calcium),
so I would recommend using the latest version which can be installed via [opam](https://opam.ocaml.org/).

## About this proof

This example proves an in-place variant of `leftpad` implemented using loops.
The latest version of Frama-C is used, version 20.0 (Calcium).
An example invocation looks like this:

```bash
$ frama-c -wp -wp-rte -warn-unsigned-overflow leftpad.c
[kernel] Parsing leftpad.c (with preprocessing)
[rte] annotating function leftpad
[wp] 56 goals scheduled
[wp] [Cache] found:31
[wp] Proved goals:   56 / 56
  Qed:              25  (2ms-26ms-88ms)
  Alt-Ergo 2.3.0:   31  (23ms-306ms-3.8s) (2273) (cached: 31)
```

The option `-wp` enables the Weakest Precondition plugin (WP).
`-wp-rte` tells WP to insert checks for run-time exceptions,
which is Frama-C parlance for undefined behavior (UB)
such as signed overflow or out-of-bounds memory access.
`-warn-unsigned-overflow` inserts checks for unsigned overflow,
which *are* defined in C, but since our loop variables are `size_t` we want checks that they don't overflow.

The output of the program tells us that all goals were proved.
Some of the proof obligations could be trivially discharged by Frama-C's built-in checker `Qed`.
The rest were verified by [Alt-Ergo](https://alt-ergo.ocamlpro.com/).
On my machine (Intel(R) Core(TM) i5-3317U CPU @ 1.70GHz) this takes just over 7.8 seconds to run.

If you have `frama-c-gui` installed, it can be invoked similarly by just replacing the name of the program:

```bash
$ frama-c-gui -wp -wp-rte -warn-unsigned-overflow leftpad.c
```

The GUI is used to assist the provers in a semi-automatic fashion, and is outside the scope of this example.

Frama-C uses [Why3](http://why3.lri.fr/) to interface with the provers,
and usually ships with Alt-Ergo as its default prover.

### Contract

First of all we'll take a look at the contract of the function:

```C
/*@ requires \valid(s + (0..n));
    requires valid_string(s);
    requires c != 0;

    behavior no_padding:
      assumes strlen(s) >= n;
      assigns \nothing;

    behavior padding:
      assumes strlen(s) < n;
      ensures valid_string(s);
      ensures \let l = strlen{Pre}(s); \let p = n - l;
        \forall integer x; 0 <= x < p ==> s[x] == c &&
        memcmp{Pre, Post}(s, s + p, l + 1) == 0 &&
        strlen(s) == n;
      assigns s[0 .. n];

    complete behaviors;
    disjoint behaviors;
 */
void leftpad(char c, size_t n, char *s) {
```

The `requires` clauses are our preconditions.
They say that we need `s` to have space for `n+1` characters,
that `s` must be a valid string and that the padding character cannot be NUL.
`valid_string` is a predicate defined internally in Frama-C in the file `__fc_string_axiomatic.h`:

```C
/*@ predicate valid_string{L}(char *s) =
  @   0 <= strlen(s) && \valid(s+(0..strlen(s)));
```

`strlen` in turn has an axiomatic definition in the same file which is too lengthy to quote here.
After the preconditions we have two so-called `behaviors`: `no_padding` and `padding`.

`no_padding` says that if the length of `s` is `n` or more then the function assigns nothing,
meaning the function has no side-effects.
This implicitly means that the length and contents of `s` remain unchanged.

The `padding` behavior says that if the length of `s` is less than `n` then `s` will be padded.
The two `ensures` clauses that follow are postconditions that specify what this means.
`valid_string(s)` means that the resulting `s` will be a valid string, just as in the preconditions.
The second clause defines the contents of `s`.
It defines two local names using `\let`, for readability:
one for the length of the input string (`l`) and another the amount of padding (`p`).
The `{Pre}` in the `strlen` predicate specifies that it is the length of `s` *when the function is called*,
not *after* it has been called. The latter would be `strlen(s)` or `strlen{Post}(s)`.
Let us take a closer look at the conjunction that makes up the rest of this postcondition:

`(\forall integer x; 0 <= x < p ==> s[x] == c)`
says that the first `p` characters in `s` are `c`.
`memcmp{Pre, Post}(s, s + p, l + 1) == 0` uses the logic function `memcmp` to say that
the contents of `s` at offset `p` is the same as the input string, including the NUL terminator.
`memcmp` is defined axiomatically in `__fc_string_axiomatic.h`:

```C
/*@ axiomatic MemCmp {
  @ logic ℤ memcmp{L1,L2}(char *s1, char *s2, ℤ n)
  @   reads \at(s1[0..n - 1],L1), \at(s2[0..n - 1],L2);
  @
  @ axiom memcmp_zero{L1,L2}:
  @   \forall char *s1, *s2; \forall ℤ n;
  @      memcmp{L1,L2}(s1,s2,n) == 0
  @      <==> \forall ℤ i; 0 <= i < n ==> \at(s1[i],L1) == \at(s2[i],L2);
  @
  @ }
  @*/
```

This definition only covers the `memcmp() == 0` case, but this is enough for our purposes.
There is a `strcmp` predicate which could be useful here,
but it sadly cannot compare strings at different labels in Calcium.
A not-in-place implementation of `leftpad` could make use of the `strcmp` predicate however.

Finally we have `strlen(s) == n` which says that the resulting string is of length `n`,
which implies that there are no NUL characters in the range `s[0..n-1]`.

The final `assigns` clause says that the `padding` behavior
has the side effect of assigning elements in the range `s[0..n]`.
In general it is possible that the function assigns only a subset of this range;
`assigns` is allowed to specify a superset of the elements actually assigned.

The final two lines in the contract specify that the `assumes` clauses cover the entire behavior of the function.
Specifically, the combination of `complete behaviors` and `disjoint behaviors` means that the preconditions imply
`strlen(s) >= n` XOR `strlen(s) < n`.
For more information about behaviors, see the ACSL manual on the Frama-C website.

### Implementation

The implementation makes use of two loops,
which are only executed if the length of the input string is less than `n`.
The first loop is equivalent to `memmove(s+p, s, l+1)` and the second loop to `memset(s, c, p)`.
Let us look closer at the first loop:

```C
/*@ loop invariant x_range: 0 <= x <= l;
    loop invariant s_state: \forall integer i; 0 <= i <= n ==>
      (i <= x+p ==> s[i] == \at(s[i], LoopEntry)) &&
      (i >  x+p ==> s[i] == \at(s[i-p], LoopEntry));
    loop assigns x, s[p..n];
    loop variant x;
 */
for (size_t x = l;; x--) {
  s[x+p] = s[x];
  if (x == 0) {
    break;
  }
}
```

This loop moves the string `p` elements to the right by starting
at the end of the string and makings its way back to `p` elements from the start.
The loop invariant `x_range` constrains the range of `x`.
The invariant `s_state` describes the contents of `s` at each iteration in the loop.
The `loop assigns` describes the side effects of the loop,
namely assigning the loop variable and the elements of `s` that the loop moves the string into.
To avoid underflowing `x` an explicit check against zero terminates the loop.
Using `ssize_t` for `x` would be an alternative solution.
The loop variant specifies that the loop terminates.
We will go into more detail about loop variants further down.

Between the loops there are three assertions:

```C
//@ assert same_chars: memcmp{Pre, Here}(s, s+p, l+1) == 0 && s[n] == 0;
//@ assert valid_str: valid_string(s+p);
//@ assert same_len: strlen(s+p) == l;
```

The purpose of these is to speed up the verification.
Try removing them and see how it impacts the time spent by `frama-c`.

The final loop inserts the padding characters at the start of the string:

```C
/*@ loop invariant x_range2: 0 <= x <= p;
    loop invariant still_same: memcmp{Pre, LoopCurrent}(s, s+p, l+1) == 0 && s[n] == 0;
    loop invariant valid_grows: valid_string(s + p - x);
    loop invariant padding_grows: \forall integer i; p - x <= i < p ==> s[i] == c;
    loop assigns x, s[0..p-1];
    loop variant p - x;
 */
for (size_t x = 0; x < p; x++) {
  s[p-1-x] = c;
}
```

`x_range2` is similar to `x_range`.
`still_same` affirms that the loop does not modify the range `s[p..n]`.
It should not be necessary, but waiting for Alt-Ergo to figure that out would take ages.
It is possible that enabling other provers such as [Z3](https://en.wikipedia.org/wiki/Z3_Theorem_Prover) (`-wp-prover z3`)
might make `still_same` redundant.
Feel free to experiment!

`valid_grows` says that the valid string grows at each iteration of the loop.
`padding_grows` similarly says that the padding grows each iteration.
Side effects are similar to the previous loop.
Finally we come to the loop variant.

A loop variant in ACSL is an expression which is positive while the loop is executing,
decreases at each iteration of the loop and becomes zero or less when the loop terminates.
This allows Frama-C to reason about program termination.
Support for verifying program complexity and termination is not supported in Frama-C at the moment (in Calcium).

### A few notes about builtins

It is possible to implement `leftpad` using `memmove` and `memset`.
Doing so requires the `-builtin` plugin, which is only available in the development version of Frama-C.
It will be available in the next version of Frama-C, Scandium.
It may also require some "handholding" of the provers via so-called *proof scripts* generated by the GUI.

### Resources

* [ACSL Mini-Tutorial](https://frama-c.com/download/acsl-tutorial.pdf)
* [ACSL 1.14](https://frama-c.com/download/acsl-implementation-20.0-Calcium.pdf)
* [WP manual](https://frama-c.com/download/wp-manual-20.0-Calcium.pdf)
* [frama-c tag on Stack Overflow](http://stackoverflow.com/tags/frama-c/)
* [Frama-c-discuss mailing list at inria.fr](http://lists.gforge.inria.fr/cgi-bin/mailman/listinfo/frama-c-discuss)

## About me

My website is [härdin.se](https://www.härdin.se/) (or haerdin.se), take a look!
I mostly write about technical things.
I have written a few posts about Frama-C and SPARK under the [formal verification tag](https://www.härdin.se/tag/formal-verification.html).
Some of the things I'm involved in include:

* [FMIGo!](https://www.fmigo.net/), a set of Free Software tools aimed at the Functional Mockup Interface (FMI) standard. Useful for distributed co-simulation
* [FFmpeg](https://www.ffmpeg.org/), maintainer of mostly broadcast-related things like the MXF codebase
* [Space Science Sweden](https://www.spacesciencesweden.se/), an Umeå based group working on an electrostatic field mill that will hitch a ride to the moon with the German company [PTS](https://www.pts.space/).
Our codebase makes considerable use of Frama-C and is available at [SpaceScienceSweden/ulv_electronics](https://github.com/SpaceScienceSweden/ulv_electronics) on GitHub.
See [verified.h](https://github.com/SpaceScienceSweden/ulv_electronics/blob/master/code/app/verified.h) and [verified.c](https://github.com/SpaceScienceSweden/ulv_electronics/blob/master/code/app/verified.c)

I'm mostly active on IRC as thardin on [FreeNode](irc://chat.freenode.net/).
I'm also on Jabber/XMPP, [tms@haerdin.se](xmpp:tms@haerdin.se).

I'm available for consulting from time to time, see [the consulting section on my website](https://www.härdin.se/pages/consulting.html).

Thanks for reading!
