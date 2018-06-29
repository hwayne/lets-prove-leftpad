# [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php)

The goal of this attempt is to define a function which is correct by construction
rather than writing the usual leftpad first and then stating and proving a lemma
about it.

## About Agda

From the Agda website:

> Agda is a dependently typed functional programming language. It has inductive
> families, i.e., data types which depend on values, such as the type of vectors
> of a given length. It also has parametrised modules, mixfix operators, Unicode
> characters, and an interactive Emacs interface which can assist the programmer
> in writing the program.

## About the proof

### Defining maximum: comparing natural numbers

The proof starts with an inductive family specifying what it means for a natural
number to be either `less than or equal' or `greater than' another one.

```agda
data LeOrGt : ℕ → ℕ → Set where
  le : ∀ m k → LeOrGt m (k + m)
  gt : ∀ m k → LeOrGt (suc k + m) m
```

The standard library already has various notions of `less than or equal` and
`greater than' for natural numbers however this one will play well with the way
`leftpad` is defined. It is always a good idea to pick the best representation
available, proving it equivalent to other ones later if need be.

We then have a proof that `LeOrGt` covers all possible cases, that is to say:
given two natural numbers, we can always compare them.

```agda
compare : ∀ m n → LeOrGt m n
```

Once we know how to compare two natural numbers, we can take the maximum: we
compare them and conclude from that! Here it may look like our efforts in
enforcing precise return indices in `LeOrGt` are wasted. But they are not:
they help us a lot in the next section!

```agda
_⊔_ : ℕ → ℕ → ℕ
m ⊔ n with compare m n
... | le _ _ = n
... | gt _ _ = m
```

### Implementing a correct-by-construction `leftpad`

We then specify the result of `leftpad` as another inductive family in a module
parametrised by the type of `characters' `A` and the padding character `x`:

```agda
data LeftPad {n : ℕ} (xs : Vec A n) : ∀ m → Vec A m → Set where
    Padded : ∀ k → LeftPad xs (k + n) (replicate {n = k} x ++ xs)
```

What this says is that an `x`-left-padded version of `xs` is any vector of the shape
`replicate x ++ xs`. This inductive family effectively defines a 4-place relation
between two natural numbers and two vectors of the corresponding lengths.

The function `leftpad` itself is the proof that given a vector `xs` of size `n` and
a natural number `m` we can always find a vector of size `n ⊔ m` related to `xs` by
the specification. The proof is direct because the result of calling `compare`
refines the goal just the right way.

```agda
leftPad : ∀ n m (xs : Vec A n) → ∃ (LeftPad xs (n ⊔ m))
leftPad n m xs with compare n m
... | le .n k = , Padded k
... | gt .m k = , Padded 0
```
