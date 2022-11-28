# [Cryptol](https://cryptol.net/)

## About Cryptol

Per its [website](https://cryptol.net/),

> Cryptol is a domain-specific language for specifying cryptographic algorithms.

It's intended for writing cryptographic algorithms in a language that more closely resembles their mathematical descriptions.
These executable specifications can serve as the formal documentation for a cryptographic module.
We can then use such executable specifications can to formally verify properties specified in Cryptol itself or to automatically verify implementations written in, say, C via [SAW](https://saw.galois.com/).

Cryptol is a strongly-typed functional language [implemented in Haskell](https://github.com/GaloisInc/cryptol); Cryptol itself resembles Haskell with the addition of being able to express arithmetic constraints on type variables.
Per the [Programming Cryptol book](https://cryptol.net/files/ProgrammingCryptol.pdf),

> Cryptol does not have a general-purpose dependent type system, but a size-polymorphic type system.

This allows one to describe, for instance, strings of a specified length.
The type system also allows expressing arbitrary relations over the type variables, such as "the length of the output string `out` is the `max` of the length of the padding `pad` and the length of the input string `in`.

The Cryptol interpreter/REPL offer a couple of commands that are useful for this exercise:

- `:check`, which checks a `property` in a randomized fashion akin to [QuickCheck](https://en.wikipedia.org/wiki/QuickCheck),
- `:exhaust`, which exhaustively checks a `property`, and
- `:prove`, which proves a `property` by calling out to SMT solvers, [Z3 by default](https://github.com/Z3Prover/z3).

## About the Proof

The actual implementation of `leftpad` resembles the [Liquid Haskell](../liquidhaskell/LeftPad.hs) implementation; without type variables, it reads `leftpad c s = repeat c # s`, which says "repeat the character `c` and append to that the original string `s`.
To specify the number of required repetitions, we include the types:

```cryptol
leftpad : {pad, in, out} Char -> String in -> String out
leftpad c s = repeat `{pad - in} c # s
```

Now, this reads "given three lengths `pad`, `in`, and `out`, a character `c`, and a string `s` of length `in`, repeat `c` (`pad` - `in`) times and append to that the original string `s`."
This still won't compile, however, as the Cryptol interpreter will complain about needing certain constraints:

```
[error]
  Failed to validate user-specified signature.
    in the definition of 'leftpad::leftpad'
    we need to show that
      for any type pad, in, out
      the following constraints hold:
        • fin in
            arising from
            use of partial type function (-)
        • fin pad
            arising from
            use of expression (#)
        • pad >= in
            arising from
            use of partial type function (-)
        • out == pad
            arising from
            matching types
```

Since we use the types `pad`, `in`, and `out` to specify lengths of strings and in functions requiring finite values, we must mark them finite with the `fin` constraint.
Moreover, because we used `pad - in` as the length of the prefix, it must be non-negative; hence `pad` must be greater than or equal to `in`.
Finally, the interpreter deduced that the length `out` must be the same as `pad`, which we can check for ourselves from our desired properties of left pad: we need `out` to be the maximum of `pad` and `in`, but `pad >= in` means that `pad` _is_ the maximum of `pad` and `in`.

For ease of reuse, let's factor our the length constraints, and then use them in our definition of `leftpad`.

```cryptol
type constraint lpCons pad in out = (fin pad, fin in, fin out, pad >= in, out == pad)

leftpad : {pad, in, out} (lpCons pad in out) => Char -> String in -> String out
leftpad c s = repeat `{pad - in} c # s
```

With this, asking `cryptol` to load the file completes without complaint:

```
$ cryptol
┏━╸┏━┓╻ ╻┏━┓╺┳╸┏━┓╻
┃  ┣┳┛┗┳┛┣━┛ ┃ ┃ ┃┃
┗━╸╹┗╸ ╹ ╹   ╹ ┗━┛┗━╸
version 2.13.0
https://cryptol.net  :? for help

Loading module Cryptol
Cryptol> :l leftpad.cry
Loading module Cryptol
Loading module leftpad
```

Now for the properties!
I'll include the first one here for our discussion; what follows will also apply to the other two properties as well.

Here's the first property in all its glory, reusing our constraint from above:

```cryptol
leftpadLength : {pad, in, out} (lpCons pad in out) => Char -> String in -> Bit
property leftpadLength c s = length (leftpad `{pad, in, out} c s) == `out
```

Recalling the constraints `lpCons`, this says that the length of our output string is `out` A.K.A. `pad` A.K.A. `max(pad, in)`.

Trying to `:prove` this property, however, the interpreter complains:

```
leftpad> :prove leftpadLength
Not a monomorphic type:
{pad, in, out}
  (fin pad, fin in, fin out, pad >= in, out == pad) =>
  [8] -> [in][8] -> Bit
(Total Elapsed Time: 0.000s)
```

Because the type `{pad, in, out}` is not monomorphic (i.e. instantiated with specific numbers in this case), `cryptol` refuses to try and prove `leftpadLength`.
Quoth [Programming Cryptol](https://cryptol.net/files/ProgrammingCryptol.pdf),

> we cannot directly prove polymorphic properties as they may hold for certain monomorphic instances while not for others. In this cases, we must tell Cryptol what particular monomorphic instance of the property we would like it to prove.

I suppose this makes sense given Cryptol's intended use.
Though we may wish to state polymorphic constraints with type variables like `pad`, `in`, and `out`, Cryptol's ultimate goal is to construct rock-solid specifications of cryptographic algorithms; in "real world implementations," one would fill in these type variables for any specific implementation.
I'm a bit saddened by this; but! We can continue by specifying values for `pad`, `in`, and `out` for the interpreter.

```
leftpad> :prove leftpadLength `{1024, 256, 1024}
Q.E.D.
(Total Elapsed Time: 0.028s, using "Z3")
```

Two interesting things.
First, if you specify an invalid `{pad, out, in}` triple, the interpreter will complain:

```
leftpad> :prove leftpadLength `{256, 256, 1024}

[error]
  • Unsolvable constraint:
      1024 == 256
        arising from
        use of expression leftpadLength
```

Second, `:prove`-ing properties via `Z3` is more exhaustive than randomized testing with `:check` and can be _much_ faster than exhaustively checking with `:exhaust`.
Cryptol treats characters as bytes (the concerns of the cryptographic domain sneaking in):

```
leftpad> 'A'
0x41
leftpad> :set ascii=on
leftpad> 'A'
'A'
```

As such, the property

```
leftpadLength `{pad, in, out}
```

is a statement about 256 * (1 + `in`) different possible combinations.
With `:check`, this can be quick but cover only a small amount of the space:

```
leftpad> :check leftpadLength `{1024, 256, 1024}
Using random testing.
Passed 100 tests.
Expected test coverage: 0.00% (100 of 2^^2056 values)
```

It's infeasible to use `:exhaust` for anything beyond small values:

```
leftpad> :exhaust leftpadLength `{2, 1, 2}
Using exhaustive testing.
Passed 65536 tests.
Q.E.D.
Testing...   9%^C
Test interrupted...
Passed 1646663 tests.
Test coverage: 9.81% (1646663 of 2^^24 values)
Ctrl-C
```

A great example of why formal methods (e.g. using `:prove` to reach out to `Z3` to formally verify our 3 properties of leftpad) is so powerful!

## About Me

Hi! I'm Graham.
I've worked as an applied research mathematician, a data scientist, and now as a quantum machine learning researcher.
You can find some more about me at my [website](https://grahamenos.com/), [GitHub](https://github.com/genos), or [Twitter](https://twitter.com/graham_enos) (assuming it still exists by the time you're reading this).
