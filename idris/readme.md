# [Idris](http://www.idris-lang.org/)

I saw the partially proven LiquidHaskell version, and thought about how the natural way to specify the output was just "padding + text" for some appropriate padding, and decided to see if I could specify it exactly that way.

## About Idris

From the Idris website:

> Idris is a general purpose pure functional programming language with dependent types.
> Dependent types allow types to be predicated on values, meaning that some aspects of a program’s behaviour can be specified precisely in the type.

In a dependently typed language, theorems are just a certain way of looking at types, and proofs of theorems are just a programs with those types.
This means that we can prove a program is correct just by giving it a precise-enough type.

## About the Proof

```idris
import Data.Vect
```

We define this `eq_max` theorem, since it's the core part of how the nice implementations of leftpad work:
You subtract your existing length from your padding, and then add it back on, and since `minus` here is saturating subtraction, this does what we want and gives the maximum of the two.

For people not familiar, implementing a recursive function with a type like this is providing an inductive proof of a theorem.
A function that takes some arguments is saying "forall," and then we're proving the equality in the result type.

```idris
eq_max : (n, k : Nat) -> maximum k n = plus (n `minus` k) k
```

The cases for `n Z` and `Z (S _)` are able to be directly proved, they're the base cases for our recursion.

```idris
eq_max  Z    (S _) = Refl
```

Every time we say `rewrite _ in _`, we're modifying the type of the value in the second position using an equality in the first position.
For example, if you wrote a function that doubled the length of a vector, you might use it to prove that `Vect (n + n) a` (from appending) is the same as a `Vect (n * 2) a`.
In this case we use it to explicitly cancel the 0 in the type of the first base case, since Idris doesn't do that for you.

```idris
eq_max  n     Z    = rewrite minusZeroRight n in rewrite plusZeroRightNeutral n in Refl
```

The final case is the inductive step.
We use our rewrites to pull the `S` out of the equation, and then we're able to prove it by the inductive hypothesis (the recursive case).

```idris
eq_max (S n) (S k) = rewrite sym $ plusSuccRightSucc (n `minus` k) k in rewrite eq_max n k in Refl
```

Now that we've got our `eq_max` theorem, we can actually define our program.
We want to implement leftpad.
What does leftpad do?
Well, we take a list (`xs`), a padding value (`x`), and a length (`n`).
If the list is smaller than the padding value, then we repeat the padding value in front of the list until it's long enough.
Symbolically, we might say that there's some number `m` such that we repeat `x` `m` times, and prepend that to list, and then the result is `max (length xs) n`.

If we want to make sure that we're implementing this correctly, one way to do this in Idris is return the result as well as a proof that it matches the spec.
The tool to use is a "dependent pair," written `(x : T ** P x)`, which says that we're returning a value of type `T` named `x`, and also that the fact `P x` is true.
(Recall, theorems are just types, and proofs are just values, so we give a proof in the second position of the pair.)
We want to say, we we start with a list `xs` of length `k`, which we write as `xs : Vect k a`, a value `x`, and a length `n`, and return a result `ys : Vect (maximum k n) a`, just like we said above in the spec.
Further extending the spec, we want to say that there's some number `m` such that `ys = replicate m x ++ xs`, also a direct translation of our spec.
Given this type, we can just write the same code we'd write in Haskell, and put the proof arguments after it.
We also need to rewrite with the `eq_max` we made earlier to make sure that the `maximum k n` in the type matches the ``n `minus` k + k`` that we get from appending the lists in the implementation.

```idris
leftPad : (x : a) -> (n : Nat) -> (xs : Vect k a)
       -> (ys : Vect (maximum k n) a ** m : Nat ** ys = replicate m x ++ xs)
leftPad {k} x n xs = rewrite eq_max n k in (replicate (n `minus` k) x ++ xs ** n `minus` k ** Refl)
```

We can skip the "existential" for the padding size and inline the ``n `minus` k``...
I'm not sure if this is better, but it's slightly smaller!

```idris
leftPad' : (x : a) -> (n : Nat) -> (xs : Vect k a)
        -> (ys : Vect (maximum k n) a ** ys = replicate (n `minus` k) x ++ xs)
leftPad' {k} x n xs = rewrite eq_max n k in (replicate (n `minus` k) x ++ xs ** Refl)
```

## About the Trusted Codebase

Some of the correctness in the standard library functions, we get for free.
For instance, I don't know if there are any explicit correctness proofs for `replicate`, but in that case, the type is precise enough that you can *only* implement it correctly.

```idris
replicate : (n : Nat) -> a -> Vect n a
```

Because of parametricity, the only value of type `a` we can get is the one that's passed to the function, and the result must be the correct length just by the index in the result type.
Therefore, it's impossible to implement `replicate` incorrectly.

Our append (the `++`) on the other hand, I couldn't find correctness proofs for, but also I don't know if I *could* really prove it correct from within Idris, without trusting something else.
Unlike some other languages where list indexing is built into their theories, Idris's indexing is just defined as a normal function, so anything proved about appending would have to rely on that also being correct.
In this case, I choose to assume that `++` is implemented correctly.

## About Me

I'm a computer science student at the University of Michigan who likes programming languages and compilers.
You can find me [on twitter](https://twitter.com/porglezomp) being a distracted nerd, or [on GitHub](https://github.com/porglezomp/) writing lots of Rust code.
