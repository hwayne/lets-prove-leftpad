# TLAPS (no temporal logic)

## Intro

This leftpad entry differs from [this
one](https://github.com/hwayne/lets-prove-leftpad/tree/master/tlaps) by not
describing a step-by-step algorithm, but describing instead the problem as you
would probably do it in "pure math". In particular, there is no time involved
(through an underlying temporal logic) in this entry.

The leftpad definition can be evaluated with
[TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) (through lemmas)
or with the TLC model checker (more on this in the line-by-line explanation
section).

Also thanks to the conciseness of TLA and power of TLAPS, this entry is only 11
line-long, while remaining quite readable (in my opinion).

## About TLAPS

The TLA+ Proof System
([TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html)) is a
mechanical proof checker for checking a [structured
proof](https://lamport.azurewebsites.net/pubs/proof.pdf)
written in TLA+.

## Setup

To test the following, you will need the TLA+ IDE, the so-called ["TLA+
Toolbox"](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4), and
[TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) version 1.5.0,
which must be installed separately.

## Line-by-line explanation

This is the whole entry:

```
------------------------------ MODULE Leftpad ------------------------------
EXTENDS Integers, Sequences
Max(i, j) == IF i < j THEN j ELSE i
Leftpad(c, n, s) == [i \in 1..Max(n, Len(s)) |-> IF i <= n - Len(s) THEN c ELSE s[i - Max(0, n - Len(s))]]
THEOREM LeftpadCorrect ==
  \A Char : \A c \in Char, n \in Nat, s \in Seq(Char) :
    /\ Len(Leftpad(c, n, s)) = Max(n, Len(s))
    /\ \A i \in 1..Max(0, n - Len(s)) : Leftpad(c, n, s)[i] = c
    /\ \A i \in DOMAIN s : Leftpad(c, n, s)[Max(0, n - Len(s)) + i] = s[i]
BY DEF Leftpad, Max
=============================================================================
```

Now the explanation. Hopefully this should be understandable by people not
knowing TLA+.

```
------------------------------ MODULE Leftpad ------------------------------
```

Every TLA+ definition must live in a module. This opens the Leftpad module.
Don't write anything before! Note that the filename must match the module name.

```
EXTENDS Integers, Sequences
```

Import integers and sequences definitions. We will encode strings as sequences
of characters. A sequence of length $n$ over a set of elements $A$ is a
(mathematical) function that assigns to each element in the range $1, 2, ..., n$
an element in $A$. Note that sequences in TLA+ index from $1$.

```
Max(i, j) == IF i < j THEN j ELSE i
```

This defines the `Max` operator for integers `i` and `j`. `<X> == <Y>` means
"`<X>` is defined to equal `<Y>`". Double-equal (`==`) must be distinguished
from single equal (`=`), which denotes the mathematical equality.

```
Leftpad(c, n, s) == [i \in 1..Max(n, Len(s)) |-> IF i <= n - Len(s) THEN c ELSE s[i - Max(0, n - Len(s))]]
```

This defines the `Leftpad` operator for padding character `c`, resulting length
`n` and to-be-padded string `s`. `Leftpad` is unconcerned with what a character
really is, so any set of "characters" will do. `Leftpad(c, n, s)` is a string,
and strings are (encoded as) sequences, which are themselves functions from a
$1..n$ range. `[<arg> \in <set> |-> <body>]` is the syntax to define a function
with one argument. In the `Leftpad` definition, `i` is the string index and
`1..Max(n, Len(s))` is its range.

```
IF i <= n - Len(s) THEN c
```

`Len(s)` is the length of the sequence `s`.

```
ELSE s[i - Max(0, n - Len(s))]
```

`<sequence>[<index>]` is the element of `<sequence>` at `<index>` (counting from
$1$!).

You can already evaluate the `Leftpad` operator for some arguments with TLC (the
TLA+ model checker). In the IDE, add a model: `TLC Model Checker > New Model... > <enter a model name>`.
In the model tab, check: `Evaluate Constant Expression > No Behavior Spec`. In
the Expression text area, write the expression to evaluate, then run (click
"play" button or hit F11).

Examples (sequences are opened by `<<` and closed by `>>`, elements are
separated by commas):

| Input                                         | Ouput                                      |
| --------------------------------------------- | ------------------------------------------ |
| `Leftpad("!", 5, <<"f", "o", "o">>)`          | `<<"!", "!", "f", "o", "o">>`              |
| `Leftpad("!", 0, <<"f", "o", "o">>)`          | `<<"f", "o", "o">>`                        |
| `Leftpad(TRUE, 4, <<FALSE, TRUE>>)`           | `<<TRUE, TRUE, FALSE, TRUE>>`              |
| `Leftpad(<<1,2>>, 4, <<<<3,4>>, <<5,6,7>>>>)` | `<<<<1,2>>, <<1,2>>, <<3,4>>, <<5,6,7>>>>` |

(See the next section for evaluating with TLAPS)

```
THEOREM LeftpadCorrect ==
```

Following the
[instructions](https://github.com/hwayne/lets-prove-leftpad/?tab=readme-ov-file#why-are-we-proving-leftpad),
we're going to prove the following points:

> 1. The length of the output is `Max(n, Len(s))`
> 2. The prefix of the output is padding characters and nothing but padding characters
> 3. The suffix of the output is the original string.

```
\A Char :
```

`\A` means "for all". The syntax is `\A <elem1> \in <set1>, <elem2> \in <set2>,
... :`. However, we write here `\A Char` without any "`\in <set>`" part. This is
because `Char` is itself a set and [there is no set of all
sets](https://en.wikipedia.org/wiki/Russell%27s_paradox). `\A Char :` indicates
the proof is going to be valid for any set of "characters".

```
\A c \in Char, n \in Nat, s \in Seq(Char) :
```

`Char` was introduced first because `c` and `s` need it. `n` is a natural number
($0, 1, ...$) and `s` is a sequence of `Char`.

```
/\ Len(Leftpad(c, n, s)) = Max(n, Len(s))
```

`/\` means "and". Several `/\` can be vertically aligned to reduce parentheses.
This line encodes the first point:

> 1. The length of the output is Max(n, Len(s))


```
/\ \A i \in 1..Max(0, n - Len(s)) : Leftpad(c, n, s)[i] = c
```

This encodes the second point:

> 2. The prefix of the output is padding characters and nothing but padding
> characters.

If `n - Len(s)` is less than `0`, `Max(0, n - Len(s))` equals `0` and `1..Max(0,
n - Len(s))` equals `1..0`, which is the empty set.

```
/\ \A i \in DOMAIN s : Leftpad(c, n, s)[Max(0, n - Len(s)) + i] = s[i]
```

This encodes the third point:

> 3. The suffix of the output is the original string.

`DOMAIN` is a built-in operator valid on functions (recall that `s` is a
sequence, which is function). Concretely, `DOMAIN s` is the range `1..Len(s)`.

```
BY DEF Leftpad, Max
```

This is the justification *per se*. We say to the prover: "Look at the
definitions of `Leftpad` and `Max` and get by with it." Now, you can run the
prover by putting the cursor anywhere inside the proof and hitting
`<Ctrl-G><Ctrl-G>` (or right-clicking `TLA Proof Manager > Prove Step or
Module`)

The proof's text goes green: the justification is accepted!

```
=============================================================================
```

This closes the Leftpad module. Don't write anything after!


## Evaluating with TLAPS

You can write lemmas to evaluate `Leftpad`. For instance:

```
LEMMA Leftpad("!", 5, <<"f", "o", "o">>) = <<"!", "!", "f", "o", "o">>
BY DEF Leftpad, Max
```

or

```
LEMMA Leftpad("!", 0, <<"f", "o", "o">>) = <<"f", "o", "o">>
BY DEF Leftpad, Max
```

or

```
LEMMA Leftpad(<<1,2>>, 4, <<<<3,4>>, <<5,6,7>>>>) = <<<<1,2>>, <<1,2>>, <<3, 4>>, <<5, 6, 7>>>>
BY DEF Leftpad, Max
```

The `BY LeftpadCorrect` justification would be preferable but it is refused for
some reasons.


## Caveat

It is very nice that the prover is content with the `BY DEF Leftpad, Max`
justification. However, this justification is quite brittle. An innocent change
in the theorem formulation could make the prover fail. Try for example to swap
`Max`'s arguments and see. In case of failure, the proof must be
[decomposed](https://lamport.azurewebsites.net/pubs/proof.pdf).


## Acknowledgements

- Thanks to [Leslie Lamport](https://en.wikipedia.org/wiki/Leslie_Lamport) for
  his clear (and useful) thinking, this is rare in the software world.

- Thanks to the TLA toolbox and TLAPS developers for their great work.

- Thanks to [Hillel Wayne](https://www.hillelwayne.com/) for his nice idea.
