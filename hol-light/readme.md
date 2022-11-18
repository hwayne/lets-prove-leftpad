# HOL-Light

HOL-Light is proof assistant by John Harrisson in the tradition of LCF.
You can find more information at https://www.cl.cam.ac.uk/~jrh13/hol-light/.

HOL-Light's old-school style prompts for a lot of uppercase. That makes
it sound more authoriative.

Like in the HOL4 proof, we are using functions on lists from the
standard library to define `LEFTPAD`. There is no nice infix syntax
for list concatenation by default; I guess because lists are not really
used a lot since HOL-Light is geared towards maths.

```
let LEFTPAD = new_definition
  `LEFTPAD n x l = APPEND (REPLICATE (n - LENGTH l) x) l`;;
```

Like in many other proof assistants, it is convenint that REPLICATE
takes as argument an "unsigned" integer (more precisely, a natural
number). That's because functions are easily defined inductively
on this datatype. Also, like in numerous formal logics, instead
of being partial on natural numbers, the subtraction returns 0 when
it is mathematically ill-defined. In fact, in all HOL-based theorem
provers functions have no choice but to be total.

## Some support definitions

I thought the spec would be natural if we could say that when the
string is padded, it's got the initial string as suffix. For this
to be phrased nicely I introduced a `DROP` function that gets rid
of a list prefix.

```
let DROP = new_recursive_definition num_RECURSION
  `(DROP 0 (l:A list) = l) /\
   (DROP (SUC n) l = DROP n (TL l))`;;
```

`TL` is the "tail" operation on lists. It looks like it should be
partial, but as I said earlier it's not. In fact, we just do not
know what `TL` returns when applied to the empty list, but it
returns something (a list)!.

I then proved a lemma that relates `DROP` and `APPEND` in the
rather obvious way. Its proof is a nice two-liner using inductive
reasoning on lists.

Finally, one theorem was missing: taking any element in bounds
of a list created by `REPLICATE` returns the replicated element.
That was surprisingly non-trival to prove, but golfing a bit
revealed a three-liner proof.

## Proving LEFTPAD

I just came up with a spec that seemed intuitive since there is no
constraint imposed. The spec is a conjunction of three properties.

```
!n (x:A) l.
  LENGTH (LEFTPAD n x l) >= n /\
  (!i. i < n - LENGTH l ==> EL i (LEFTPAD n x l) = x) /\
  DROP (n - LENGTH l) (LEFTPAD n x l) = l
```

  1. The length of the padded list is at least `n`, the input
     number.
  2. Any element with index less then `n - LENGTH l` in the
     output is `x`.
  3. If we drop the prefix of length `n - LENGTH l`, we end
     up with the input list.

All conjuncts are proved by the same proof script. I inserted
comments to make the split of the script more apparrent. But
following the style of the HOL-Light distributtion, the script
is nice and dense.

I hit some trouble when proving property 3 because my lemma
about dropping on an append is not flexible enough: it can
only be used as rewrite when the number of elements dropped
is of the form `(LENGTH l1)`, and that is not the case in
my goal. One preliminary targeted rewrite was sufficient to
clear the goal, but the better solution would have been to
make the `DROP_APPEND` lemma more flexible.

## Using HOL-Light

Using HOL-Light is not a piece of cake, but because I like
toying with it so much I built some tooling that you may
find useful.

HOL-Light works in an OCaml toplevel and, each time you start
it, the toplevel must ingest a vast amount of OCaml code. That
is slow. To speed things up, you can use a snapshotting library
that will serialize your loaded toplevel into an executable
you can use afterwards. I wrote such a snapshotting library that
works for C, OCaml (and HOL-Light), you can find it there:
https://c9x.me/git/selfie.git/.

Then comes the question of interacting with the toplevel in a
nice fashion. I use vim for most of my programming and so I wrote
a bit of tooling to have it communicate with an OCaml toplevel.
The plugin is here: https://github.com/mpu/vim-hol.

Have fun!
