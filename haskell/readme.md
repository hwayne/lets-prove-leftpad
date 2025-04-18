## Haskell

This is a Haskell-based solution of the `leftpad` problem. The code as a build artifact is available at [this repo](https://github.com/Abhiroop/leftpad/tree/master). Simply clone and run `cabal run` on your terminal and it should work. Tested with GHC version 9.6.7.

### About Haskell

There is very little to say about Haskell, especially in this repo, where it ends up being one of the more vanilla languages in the lineup.

Of course, any "proof" written in Haskell is inherently unsound because the language permits bottom values (such as `undefined` or `error`), which can inhabit any type, and its non-totality allows infinite loops. However, if one is ready to discount these factors, this example shows how one can exploit a single key type-level programming feature - `Close Type Families` - to write correct-by-construction code.

Also, I believe this is the only solution in this repo that uses a mainstream Turing-complete language without resorting to any external tools (like an SMT solver) to do the proof, keeping the TCB minimal. (The `java` solution uses OpenJML, which employs an SMT solver). Also, this solution relies on no external Haskell libraries - simply the `base` from GHC 9.6.7.

### About the proof

The code is heavily documented for readability. The entire leftpad computation is done at the type-level such that I can move structural constraints (such as spec (i)) as well as relational constraints (specs (ii) and (iii)) at the type-level. Size-indexed vectors are typically sufficient for spec (i), but to capture (ii) and (iii) I used `Symbol` from `GHC.TypeLits` and its associated type families such as `ConsSymbol`, `AppendSymbol`, `UnconsSymbol` to do the string manipulation. The key leftpad operation is small enough to be shown here:

```haskell
-- | A type-level replicate function
type family Replicate (n :: Nat) (c :: Char) :: Symbol where
  Replicate 0 c = ""
  Replicate n c = ConsSymbol c (Replicate (n - 1) c)

-- | A type-level computation of the pad value
type family PadK (n :: Nat) (strlen :: Nat) :: Nat where
  PadK n strlen = If (n <=? strlen) 0 (n - strlen)

-- | Use `AppendSymbol` to append the pad string using Replicate and PadK
type family PrependReplicate (c :: Char)     (n :: Nat)
                             (strlen :: Nat) (s :: Symbol) :: Symbol where
  PrependReplicate c n strlen s = AppendSymbol (Replicate (PadK n strlen) c) s
```

The rest of the code is dedicated to checking the 3 specification and I demarcate them clearly in the code. A type-level assertion is defined as the type family `Assert`. We use it to provide meaningful (type level) error messages. The code is very intentionally broken into smaller type families with helpful comments to allow the reader to understand how each spec is enforced.

After defining the 3 specifications we enforce it in the final term-level function (with the type-level constraints) as:

```haskell
leftPad :: forall c n s strlen full.
           ( full ~ PrependReplicate c n strlen s -- like a type-level `let`
           , PadKMaxEqualConstraint n strlen      -- Spec 1
           , ValidatePrepend c n strlen s         -- Spec 2
           , ValidateSuffix  c n strlen s         -- Spec 3
           , KnownSymbol full -- used for `reifying` the type-level symbol
           )
        => Proxy s
        -> Proxy strlen
        -> String
leftPad _ _ = symbolVal (Proxy @full)
```

An interesting function here is `symbolVal`, whose type is `symbolVal :: forall (n :: Symbol) proxy. KnownSymbol n => proxy n -> String`. This function is used to `reify` the final type level computed value to the term-level as the last step. This has resemblance to the `reify` operation used in Normalisation by Evaluation (a type-theoretic technique used in dependent-typed languages' typecheckers).

I tried my best to keep the trusted code base as minimal as possible, to the point of not including any external Haskell libraries as well. I am sure the `singletons` library will have some elegant approach to encode this but I think this solution is already clean enough. It doesn't use too many language extensions and unlike a previous solution, I do not invoke Multi-Parameter Typeclasses or even GADTs. Everything is encoded using a single key type-level feature — type families — to the extent that one can find an almost one-to-one correspondence at the type level with the well-known term-level operations. Except at the type-level, computations are typically encoded using a decidable logic fragment (I had to invoke `UndecidableInstances` because the GHC typechecker's termination checker is not sophisticated enough like Agda).


The API to call this function is slightly awkward at present. It approximately looks like the following:

```
leftPad @'!' @5 (Proxy @"foo") (Proxy @3)
```

The padding character and the pad length are supplied as type variables. `@` is type application. The string and its length are wrapped in corresponding `Proxy n` types to lift them to the type level.


### About me

I am [Abhiroop](https://abhiroop.github.io/), a postdoctoral researcher at ETH Zurich, where I work at the [Information Security Group](https://infsec.ethz.ch/) on applying type systems as well as runtime verification techniques to security problems.