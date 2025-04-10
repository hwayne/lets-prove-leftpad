## Haskell

This is a Haskell-based solution of the `leftpad` problem. The code with its build dependencies is available in [this repo](https://github.com/Abhiroop/leftpad/tree/master). Simply clone this and run `cabal run` on your terminal and it should work. Tested with GHC version 9.2.8.

### About Haskell

There is very little to say about Haskell, especially in this repo, where it ends up being one of the more vanilla languages in the lineup.

Of course, any "proof" written in Haskell is inherently unsound because the language permits bottom values (such as `undefined` or `error`), which can inhabit any type, and its non-totality allows infinite loops. However, if one is ready to discount these factors, this example shows how relatively old language extensions in Haskell like `GADTs`, `Type Families` and `Multi Parameter Typeclasses` (almost all of them introduced before 2006), can promote writing correct-by-construction code.

Also, I believe this is the only solution in this repo that uses a mainstream Turing-complete language without resorting to any external tools (like an SMT solver) to do the proof, keeping the TCB minimal. (The `java` solution uses OpenJML, which employs an SMT solver).

### About the proof

The proof is quite small and should be fairly self-explanatory. The 3 specification parameters asked in the original problem is captured using these two type families:

```haskell
-- capture (i)
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = If (a <=? b) b a

-- capture (ii) and (iii)
type family PadK (pad :: Nat) (n :: Nat) :: Nat where
  PadK pad n = If (pad <=? n) 0 (pad - n)
```

The solution uses the [`vector-sized`](https://hackage.haskell.org/package/vector-sized) library for length-indexed vectors. There is no reason to use this particular library. Its easily possible to roll out your own sized vector implementation, but the library provides a nice Prelude to work with sized vectors.

Written modularly, I defined a `padString` function that produces a length index vector representing the pad prefix, further constrained by the type family `PadK`. The only challenging part of this implementation was when combining this pad prefix with the original string, requires triggering a type level computation that shows `(PadK pad n) + n ~ Max pad n`. I accomplish this using the following multi-parameter typeclass, which constrains the final result:

```haskell
class ((PadK pad n) + n ~ Max pad n) => PadKMaxEqual (pad :: Nat) (n :: Nat)
instance ((PadK pad n) + n ~ Max pad n) => PadKMaxEqual pad n
```

The API to call this function is slightly awkward at presnt. It looks like the following

```
leftPad '!' (Proxy @5) (Proxy @3) "foo"
```

The padding value and the length of the string being supplied has to be wrapped into a `Proxy n` type. This can be abstracted over using a CPS transform but is besides the problem at hand.

