# [Metamath](http://us.metamath.org/)

"Metamath is a simple and flexible computer-processable language that supports rigorously verifying, archiving, and presenting mathematical proofs. Metamath has a small specification that enables you to state a collection of axioms (assumptions), theorems, and proofs (aka a "database"). We have databases for several axiomatic systems. "

## About Metamath

Metamath verifiers have been independently implemented by different people in different programming languages, reducing the risk of accepting an invalid proof.

Metamath is not tied to any particular set of axioms, instead, axioms are defined in a database.
This proof of leftpad is now part of the classical-logic, ZFC-based database, [`set.mm`](https://us.metamath.org/mpeuni/mmset.html). Another well-developped database is based on the intuitionistic logic.

## About the Proof

Metamath proofs include every step, no exceptions, where each step is only an application of an axiom or a previously-proved statement. 
The `set.mm` database already includes a section about the free monoid, where strings, i.e. words over sets, are represented as function, and the concatenation operation is defined. This implementation of `leftpad` uses those concepts.

The definition and proofs for `leftpad` are available in a readable step-by-step format on the [Metamath website](http://us.metamath.org/):
- [`df-lpad`, the definition](https://us.metamath.org/mpeuni/df-lpad.html)
- [`lpadmax`, about the length of the operation result](https://us.metamath.org/mpeuni/lpadmax.html)
- [`lpadleft`, the prefix of the operation result is padding characters](https://us.metamath.org/mpeuni/lpadleft.html)
- [`lpadright`, the suffix of the operation result is the original word](https://us.metamath.org/mpeuni/lpadright.html)

## About the tools

Metamath is the language, several different tools can be used to process or build Metamath databases, at your choice. 

Before using any tool, in order to load and verify the `leftpad.mm` file, you'll need to download the main `set.mm` database, which `leftpad.mm` loads like a library. Right-click on [this link](https://raw.githubusercontent.com/metamath/set.mm/aefacec62000363b9e8d3b3c4113d52a419fb7aa/set.mm) and choose "Save As", or on a POSIX-prompt using wget:
```
wget https://raw.githubusercontent.com/metamath/set.mm/aefacec62000363b9e8d3b3c4113d52a419fb7aa/set.mm
```
(the long SHA code points to a commit which is known to work for `leftpad.mm`)

The original [Metamath-exe](https://github.com/metamath/metamath-exe) verifier and proof assistant is a C program. You can install it following these instructions, launch it with `leftpad.mm` as an argument to load that database, and :
```
$ metamath
Metamath - Version 0.199.pre 29-Jan-2022      Type HELP for help, EXIT to exit.
MM> READ leftpad.mm
Reading source file "leftpad.mm"... 7222 bytes
Reading included file "set.mm"... 43445747 bytes
43453004 bytes were read into the source buffer.
The source has 207073 statements; 2798 are $a and 41200 are $p.
No errors were found.  However, proofs were not checked.  Type VERIFY PROOF *
if you want to check them.
MM> VERIFY PROOF *
0 10%  20%  30%  40%  50%  60%  70%  80%  90% 100%
..................................................
All proofs in the database were verified.
```


Another verifier is the Rust-based `metamath-knife`. [Once Rust's cargo is installed](https://doc.rust-lang.org/cargo/getting-started/installation.html), the commands to run it are:
```
cargo install --git https://github.com/metamath/metamath-knife 
metamath-knife -vt leftpad.mm 
```

There are many other verifiers and proof assistants. The list has [22 verifiers](https://us.metamath.org/other.html#verifiers) as of writing.

## About the project

The Metamath community is active and alive, and we welcome and encourage new contributors. Feel free to check our [mailing list](https://groups.google.com/g/metamath), and [main GitHub repository](https://github.com/metamath/set.mm) where many discussions take place. As of writing, [74 of a list of 100 major theorems](https://us.metamath.org/mm_100.html) have been formally proved using Metamath. Maybe you have what it takes to add yours?

## More details and explanations

### Definition of `leftpad`
Character strings in `set.mm` are formalized as functions from integer intervals starting at zero to the character set.
In order to formalize the repetition of `n` time a character `C`, a constant function from the interval `0 ... (n - 1)` is used.

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
A first function takes a length `L` and builds the left-padded string. The domain of that function is `NN0`, the set of non-negative integers. We're using lowercase letters here for free variables. Metamath limits itself to ASCII characters, so `∈` is written as `e.`.  This first function is written:
```
( l e. NN0 |-> ( ( ( 0 ..^ ( l - ( # ` W ) ) ) X. { C } ) ++ W ) )
```

The complete function takes the two other arguments, the character `C` and the length `L`, and returns the first function. In order to keep the definition generic, we don't constrain `C` and `L` other than requiring that they are sets, i.e. elements of the universal class `_V`. This is the complete expression you'll find in the definition of `leftpad`:
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

The main theorems used for this proof are the application of a function ([`~fvmptf`](https://us.metamath.org/mpeuni/fvmptd.html)) and an operation (`~ovmpt2d`)[https://us.metamath.org/mpeuni/ovmpt2d.html] to get their values. The rest is explicit substitution rules.

### Theorem `lpadmax`

There is no function for getting the maximum of two number in `set.mm`, but one can easily write the same using an `if` construct, as in `if ( A < B , B , A ) `.
```
lpadmax $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) ) = if ( L <_ ( # ` W ) , ( # ` W ) , L ) )
```
The proof relies on two lemmas, one for each case ([`~lpadlen1`](https://us.metamath.org/mpeuni/lpadlen1.html) and [`~lpadlen2`](https://us.metamath.org/mpeuni/lpadlen2.html)). In one case the prefix is reduced to the empty word, and prepending the empty word leaves any word unchanged by [`~ccatlid`](https://us.metamath.org/mpeuni/ccatlid.html). In the other case, the length is reduced to ``( ( L - ( # ` W ) ) + ( # ` W ) )``, which is then simplified thanks to [~npcand](https://us.metamath.org/mpeuni/npcand.html).

### Theorem `lpadleft`

The statement of the theorem expresses that any character with an index in the range ``( 0 ..^ ( L - ( # ` W ) ) )`` is `C`:
```
lpadleft.1 $e |- ( ph -> N e. ( 0 ..^ ( L - ( # ` W ) ) ) )
lpadleft $p |- ( ph -> ( ( ( C leftpad W ) ` L ) ` N ) = C )
```
This is obtained by first extracting the prefix using [`~ccatval1`](https://us.metamath.org/mpeuni/ccatval1.html), which results in a constant function, and then evaluating that constant function using [~fvconst2g](https://us.metamath.org/mpeuni/fvconst2g.html).

### Theorem `lpadright`

The proof is very similar to that of `lpadleft`. Interesting is that the characters of `W` are found in the left-padded result, shifted by an amount of `M` characters. The value of `M` is defined as part of the hypothesis to obtain a simpler final statement.
```
lpadright.1 $e ( ph -> M = if ( L <_ ( # ` W ) , 0 , ( L - ( # ` W ) ) ) )
lpadright.2 $e ( ph -> N e. ( 0 ..^ ( # ` W ) ) )
lpadright $p ( ph -> ( ( ( C leftpad W ) ` L ) ` ( N + M ) ) = ( W ` N ) )
```