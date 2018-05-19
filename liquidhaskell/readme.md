# [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell-blog/)

## About LiquidHaskell

LiquidHaskell is a static verifier for Haskell, based on Liquid Types which
refines Haskell's types with logical predicates that let you specify and 
verify properties at compile time. 

See[the blog](https://ucsd-progsys.github.io/liquidhaskell-blog/) for more details.

You can [run LH on the LeftPad proof here](http://goto.ucsd.edu:8090/index.html#?demo=LeftPad.hs).

## About the Proof

The implementation and proof is in [LeftPad.hs](LeftPad.hs).
Read below, or the [blog post][blog] for a detailed explanation
about the proof.

The most unique aspect about this proof relative to those using dependent 
types or proof assistants (e.g. Coq, Isabelle, Idris), is the use of 
SMT-based decision procedures for automating reasoning over arithmetic.

Dually, the most unique aspect relative to those using SMT solvers 
(e.g. Dafny, F-star, Spark), is to _limit_ SMT queries to decidable 
logics -- where SMT solvers behave in a predictable manner --  by 
eschewing axioms and quantifiers, instead using a form of type-level computation 
that we call [proof by logical evaluation](https://arxiv.org/pdf/1711.03842).

## About Me 

I am [Ranjit Jhala](https://twitter.com/RanjitJhala), one of the 
developers of LH and a professor of Computer Science and Engineering 
at the [University of California, San Diego](http://ranjitjhala.github.io/).


## The Implementation 

First, lets write an idiomatic implementation 
of `leftPad` where we will take the liberty of
generalizing 

- the **padding character** to be the input `c` that 
  is of some (polymorphic) type `a` 
- the **string** to be the input `xs` that is a list of `a`

If the target length `n` is indeed greater than the input string `xs`, 
i.e. if `k = n - size xs` is positive, we `replicate` the character `c`
`k` times and append the result to the left of the input `xs`. 
Otherwise, if `k` is negative, we do nothing, i.e. return the input.

```haskell
{-@ reflect leftPad @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad n c xs
  | 0 < k     = replicate k c ++ xs
  | otherwise = xs
  where
    k         = n - size xs
```

The code for `leftPad` is short because we've
delegated much of the work to `size`, `replicate`
and `++`, shown below:

```haskell
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size []     = 0
size (x:xs) = 1 + size xs

{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] ->
            {v:[a] | size v = size xs + size ys}
  @-}
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a ->
                 {v:[a] | size v = n}
  @-}
replicate 0 _ = []
replicate n c = c : replicate (n - 1) c
```

## An "Obviously Correct" Specification

The below type signature is a specification 
that says that for all `n`, `c` and `xs`, the value 
returned by `leftPad n c xs` is `xs` when `n` is 
too small, and the suitably padded definition otherwise. 

```haskell
{-@ obviously :: n:Int -> c:a -> xs:[a] -> 
      { leftPad n c xs = if (size xs < n) 
                         then (replicate (n - size xs) c ++ xs) 
                         else xs } 
  @-}
obviously _ _ _ = () 
``` 

The code, namely `()`, is the proof. 
LH is able to trivially check that `leftPad` 
meets the "obviously correct" specification, 
because, well, this case, the implementation 
_is_ the specification. (Incidentally, this 
is also why the [Idris solution][idris-leftpad] 
is terse.)

## Hillel's Specifications

However, the verification rodeo is made more 
interesting by Hillel's [Dafny specifications][dafny-leftpad]:

1. **Size** The `size` of the returned sequence is the 
   larger of `n` and the size of the input `xs`;

2. **Pad-Value** Suppose `n > size xs`, and let 
   `K = n - size xs`. We require that the `i`-th 
   element of the padded-sequence equals `c` if 
   `0 <= i < K`, and equals the `i - K`-th 
   element of `xs` otherwise.

## Properties of Sequences 

To specify and verify the above properties,
we need to _state_ and _prove_ relevant 
properties about sequences from scratch.

### Indexing into a Sequence

To start, lets define the notion of the `i`-th element of 
a sequence (this is pretty much Haskell's list-index operator)

```haskell
{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(x:_)  !! 0 = x 
(_:xs) !! n = xs !! (n - 1)
```

### Replicated Sequences

Next, we verify that _every_ element in a `replicate`-d 
sequence is the element being cloned:

```haskell
{-@ thmReplicate :: n:Nat -> c:a -> i:{Nat | i < n} -> 
                    { replicate n c !! i  == c } 
  @-}
thmReplicate n c i 
  | i == 0    = ()
  | otherwise = thmReplicate (n - 1) c (i - 1) 
```

LH verifies the above "proof by induction": 

- In the base case `i == 0` and the value returned is `c` 
  by the definition of `replicate` and `!!`. 
  
- In the inductive case, `replicate n c !! i` is equal to 
  `replicate (n-1) c !! (i-1)` which, by the "induction hypothesis" 
  (i.e. by recursively calling the theorem) is `c`.

### Concatenating Sequences

Finally, we need two properties that relate 
concatenation and appending, namely, the 
`i`-th element of `xs ++ ys` is: 

- **Left** the `i`-th element of `xs` if `0 <= i < size xs`, and 
- **Right** the `i - size xs` element of `ys` otherwise.

```haskell
{-@ thmAppLeft :: xs:[a] -> ys:[a] -> {i:Nat | i < size xs} -> 
                  { (xs ++ ys) !! i == xs !! i } 
  @-} 
thmAppLeft (x:xs) ys 0 = () 
thmAppLeft (x:xs) ys i = thmAppLeft xs ys (i-1)      

{-@ thmAppRight :: xs:[a] -> ys:[a] -> {i:Nat | size xs <= i} -> 
                   { (xs ++ ys) !! i == ys !! (i - size xs) } 
  @-} 
thmAppRight []     ys i = () 
thmAppRight (x:xs) ys i = thmAppRight xs ys (i-1)      
```

Both of the above properties are proved by induction on `i`.

## Proving Hillel's Specifications

### Size Specification

The size specification is straightforward, in that LH proves 
it automatically, when type-checking `leftPad` against the 
signature:

```haskell 
{-@ leftPad :: n:Int -> c:a -> xs:[a] -> 
                {res:[a] | size res = max n (size xs)} 
  @-}
```

### Pad-Value Specification

We _specify_ the pad-value property -- i.e. the `i`-th
element equals `c` or the corresponding element of `xs` --
by a type signature:

```haskell
{-@ thmLeftPad
      :: n:_ -> c:_ -> xs:{size xs < n} -> i:{Nat | i < n} ->
         { leftPad n c xs !! i ==  leftPadVal n c xs i }
  @-}

{-@ reflect leftPadVal @-}
leftPadVal n c xs i 
  | i < k     = c 
  | otherwise = xs !! (i - k)
  where k     = n - size xs 
```

### Pad-Value Verification

We _verify_ the above property by filling in the
implementation of `thmLeftPad` as:

```haskell
thmLeftPad n c xs i 
  | i < k     = thmAppLeft  cs xs i `seq` thmReplicate k c i
  | otherwise = thmAppRight cs xs i
  where 
    k         = n - size xs
    cs        = replicate k c
```

The "proof"  -- in quotes because its
just a Haskell function -- simply combines
the replicate- and concatenate-left theorems
if `i` is in the "pad", and the concatenate-right
theorem, otherwise.

[blog]: https://ucsd-progsys.github.io/liquidhaskell-blog/2018/05/17/hillel-verifier-rodeo-I-leftpad.lhs/