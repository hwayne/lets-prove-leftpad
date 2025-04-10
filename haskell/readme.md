## Haskell

This is a Haskell-based solution of the `leftpad` problem. The code with its build dependencies is available in [this repo](https://github.com/Abhiroop/leftpad/tree/master). Simply clone this and run `cabal run` on your terminal and it should work. Tested with GHC version 9.2.8.

### About Haskell

There is very little to say about Haskell, especially in this repo, where it ends up being one of the more vanilla languages in the lineup.

Of course, any "proof" written in Haskell is inherently unsound because the language permits bottom values (such as `undefined` or `error`), which can inhabit any type, and its non-totality allows infinite loops. However, if one is ready to discount these factors, this example shows how relatively old language extensions in Haskell like `GADTs`, `Type Families` and `Multi Parameter Typeclasses` (almost all of them introduced before 2006), can promote writing correct-by-construction code.

Also, I believe this is the only solution in this repo that uses a mainstream Turing-complete language without resorting to any external tools (like an SMT solver) to do the proof, keeping the TCB minimal. (The `java` solution uses OpenJML, which employs an SMT solver).

### About the proof

The proof is quite small and should be fairly self-explanatory. To capture the 3 specification we use two type families:

```haskell
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = If (a <=? b) b a

type family PadK (pad :: Nat) (n :: Nat) :: Nat where
  PadK pad n = If (pad <=? n) 0 (pad - n)
```

The solution uses the [`vector-sized`](https://hackage.haskell.org/package/vector-sized) library for length-indexed vectors. There is no reason to use this particular library. Its easily possible to roll out your own sized vector implementation, but the library provides a nice Prelude to work with sized vectors.

Written modularly, I defined a `padString` function that produces a length-indexed vector representing the pad prefix, further constrained by the type family `PadK`. `PadK` ensures that the pad string is `""` if the pad length, `pad`, is less than or equal to the string length, `n`, otherwise it pads by the amount `pad - n`. This computation is entirely done at the type level, such that the function body creates the pad string entirely directed by the type-level value. This part captures the specification (ii) and (iii).

For capturing specification (i), we find that specification (ii) and (iii) results that the final string length is always `max (pad, n)`. This is captured using the `Max` type family. The key challenging part of this implementation was when combining the pad prefix with the original string, requires triggering a type level computation that shows `(PadK pad n) + n ~ Max pad n`. I accomplish this using the following multi-parameter typeclass, which constrains the final result:

```haskell
class ((PadK pad n) + n ~ Max pad n) => PadKMaxEqual (pad :: Nat) (n :: Nat)
instance ((PadK pad n) + n ~ Max pad n) => PadKMaxEqual pad n
```

This solution is closest to the `Idris`-based solution. The API to call this function is slightly awkward at present. It approximately looks like the following:

```
leftPad '!' (Proxy @5) (fromList "foo" :: Vector 3 Char)
```

The padding value has to be wrapped into a `Proxy n` type to lift it at the type-level, and the string length has to be annotated, again for the purposes of type-level computations. A clarification to reduce any source of confusion: I call the variable `n` in the original specification as `pad` and `len(str)` as `n`.


### About me

I am [Abhiroop](https://abhiroop.github.io/), a postdoctoral researcher at ETH Zurich, where I work at the [Information Security Group](https://infsec.ethz.ch/) on applying type systems as well as runtime verification techniques to security problems.