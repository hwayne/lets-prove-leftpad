# [Metamath](http://us.metamath.org/)

"Metamath is a simple and flexible computer-processable language that supports rigorously verifying, archiving, and presenting mathematical proofs. Metamath has a small specification that enables you to state a collection of axioms (assumptions), theorems, and proofs (aka a "database"). We have databases for several axiomatic systems. "

## About Metamath

Metamath verifiers have been independently implemented by different people in different programming languages, reducing the risk of accepting an invalid proof.

Metamath is not tied to any particular set of axioms, instead, axioms are defined in a database.
This proof of leftpad is now part of the classical-logic, ZFC-based database, [`set.mm`](https://us.metamath.org/mpeuni/mmset.html). Another well-developped database is based on the intuitionistic logic.

## About the Proof

The definition and proofs are available on the [Metamath website](http://us.metamath.org/):
- [`df-lpad`, the definition](https://us.metamath.org/mpeuni/df-lpad.html)
- [`lpadmax`, about the length of the operation result](https://us.metamath.org/mpeuni/lpadmax.html)
- [`lpadleft`, the prefix of the operation result is padding characters](https://us.metamath.org/mpeuni/lpadleft.html)
- [`lpadright`, the suffix of the operation result is the original word](https://us.metamath.org/mpeuni/lpadright.html)

### Definition of `leftpad`
Character strings in `set.mm` are formalized as functions from integer intervals starting at zero to the character set.
In order to formalize the repetition of `n` times a character `C`, a constant function from the interval `0 ... (n - 1)` is used.

Here the number of repetitions should be the target length `L`, minus the length of the original word `W`:
```
( L - ( # ` W ) )
```

A left-close, right-open integer interval is expressed in `set.mm` using the `..^` operator, therefore this interval is written as:
```
( 0 ..^ ( L - ( # ` W ) ) )
```

A function is formalized as a set of pairs "<argument, value>".  When the function is constant, this is in fact the cross-product of the domain and a singleton containing the unique value:
```
( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } )
```

Finally, the repetition of the constant is concatenated with the original word ` W `. The symbol for the concatenation operation is `++`:
```
( ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) ++ W )
```

The `leftpad` function takes 3 arguments: a character, a length, and a word. There is no formal definition in `set.mm` for functions of 3 arguments, but we can use currying and functions of 2 arguments.
A first function takes a length `l` and builds the left-padded string. The domain of that function is `NN0`, the set of non-negative integers. We're using lowercase letters here for free variables. Metamath limits itself to ASCII characters, so `∈` is written as `e.`.  This first function is written:
```
( l e. NN0 |-> ( ( ( 0 ..^ ( l - ( # ` W ) ) ) X. { C } ) ++ W ) )
```

The complete function takes the two other arguments, the character `c` and the word `w`, and returns the first function. In order to keep the definition generic, we don't constrain `c` and `l` other than requiring that they are sets, i.e. elements of the universal class `_V`. This is the complete expression you'll find in the definition of `leftpad`:
```
( c e. _V , w e. _V |-> ( l e. NN0 |-> ( ( ( 0 ..^ ( l - ( # ` w ) ) ) X. { c } ) ++ w ) ) )
```

### Theorem `lpadval`
In the theorems to be proved, we're not interested in the function itself, but rather its value. Our first theorem therefore simply extracts the value of the `leftpad` function for given arguments, by applying two evaluations, and the required explicit substitutions.

In order to be able to evaluate the function, the arguments have to be sets. We further restrict them to the domains we will actually use. The argument `W` shall be a word over a given set `S`. This is expressed as ` W e. Word S`. The repeated character should itself be an element of `S`: `C e. S`.

It is convenient in many cases to prove theorems in the deductive form, i.e. when both its statement and its hypotheses are derived from a common condition `ph`, so they are written:
```
h1::lpadval.1   |- ( ph -> L e. NN0 )
h2::lpadval.2   |- ( ph -> W e. Word S )
h3::lpadval.3   |- ( ph -> C e. S )

lpadval |- ( ph -> ( ( C leftpad W ) ` L ) = ( ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) ++ W ) )
```

### Theorem `lpadmax`

TBC 

### Theorem `lpadleft`

TBC 

### Theorem `lpadright`

TBC
