# [SPARK](https://www.adacore.com/sparkpro)

## About SPARK

SPARK is both the name of a programming language and the tool which allows the
programmer to prove properties of SPARK programs.

SPARK the language is a subset of the Ada language. Ada is a general purpose
programming language, but it is mostly used in embedded and safety-critical
applications. It is an imperative language like C++, but with a stronger and
more precise type system, and clearer syntax.

SPARK is like Ada, but with a few features removed, to remove sources of
mistakes and improve the applicability of static analysis. For example,
pointers have been removed from the SPARK subset, as they make verification
more difficult even in simple cases, and are a source of many bugs. Many
language features like built-in arrays and parameter modes make pointers less
useful in SPARK than in other languages. When they are still needed, one can
step out of the SPARK subset into full Ada for some part of the program, but
cannot apply static analysis/proof to this part of the program.

SPARK is used whenever even more guarantees are required, in highly critical
parts of an embedded application, or in a security context.

SPARK proofs are based on pre- and postconditions (contracts in SPARK terms),
and use SMT solvers to prove the verification conditions. In this respect it
is similar to Dafny. However, SPARK contracts are executable, so that one can
also check them dynamically if one wishes.

SPARK is co-developed by [Altran](https://www.altran.com/uk/en/) and
[AdaCore](https://www.adacore.com/). It is a commercial application, but it is
fully open source, and a [GPL version](https://www.adacore.com/download) is
available.


## About Me

My name is Johannes Kanig, and I'm member of the development team of SPARK at
AdaCore.


## About the proof

The idea of program proof is to express the same thing twice, once as a
specification, and once as the actual program, and showing that the latter is
the same as the former. The specification can either be given as an expression
(or pure function) that computes the same thing as the program. In this case,
one usually uses the fact that the specification is not executed to write more
succinct and clearer, but less efficient code. Or, one can write the
specification in a predicate style, where one expresses the relation between
input and output of a function, but not explaining how one should derive one
from the other.

Ada (and thus SPARK) has built-in concatenation of arrays and strings, using
the `&` operator. So leftpad can be simply implemented as
```
   padding & string
```
where the only difficulty lies in computing the amount of padding required.

In a real SPARK program, because it's built-in, one would probably not write
the padding function in the first place, because it's just a simple
concatenation. Or one would write it as a pure function (or expression
function in SPARK terms), and can use it directly without doing any proofs.
But for the purposes of the leftpad exercise, I wanted to actually prove
something.

So I had two choices:

 1) I could use the above concatenation as the specification of leftpad, and
    use a loop in the implementation;

 2) I could use the above concatenation as the implementation of leftpad, and
 write the specification in predicate style.

I decided to do (2) above for the reason that it wouldn't be very idiomatic
SPARK to write the code using a loop to implement concatenation.

As we already have the implementation (it is in the `padding.adb` file), all
there is to do is to write the specification of leftpad in predicate style (in
`padding.ads`).

The postcondition looks like this, where the argument of the function is
called `S`, and the result of is written as `Left_Pad'Result` (we only mention
the case where padding is actually required):

```
        Left_Pad'Result'Length = Len and then
        (for all I in Left_Pad'Result'Range =>
           Left_Pad'Result (I) =
             (if I <= Len - S'Length then Pad_Char
              else S (I - (Len - S'Length + 1) + S'First)))
```
Some explanations:
- For a string `S`, one can write `S'Length` to get its length.
- `and then` is conjunction.
- So the first part of the conjunction simply states that the result of the
  function is of the expected length.
- To access a character at position `I` of the string `S`, (this is *not* the ith
  character as per the next point) one writes `S (I)`.
- Strings in Ada are not 0-based nor 1-based, the user can choose the bounds
  freely. We have written `Left_Pad` in such a way that it accepts strings
  with arbitrary bounds, but returns 1-based strings (the most common usage in
  Ada). This makes it necessary to do some gymnastics to determine the correct
  index in the argument string `S`. Bounds of strings are written `S'First` and
  `S'Last`.
- So the second part of the conjunction states that the ith character of the
  result (the result is 1-based, so it's indeed the ith character) is a
  padding character if `I` is smaller than some value, otherwise equal to the
  input string `S` at some specific position.

Like in Dafny, no manual proof is necessary. Everything is proved
automatically in this simple example.

## How to run the proof

Follow these steps to reproduce the proof:

1) Download and install the [SPARK Discovery GPL package](https://www.adacore.com/download). Don't forget to put the `bin` folder of the install in your `PATH`.

2) run

```
  gnatprove -P test.gpr --steps=0
```

Explanations:

 - `gnatprove` is the name of the commandline tool of SPARK
 - `-P test.gpr` indicates the name of the project File, which is called
   test.gpr
 - By default, SMT provers are allowed a certain small number of reasoning
   steps, which is not sufficient in this example. With the argument
   `--steps=0`, we disable this limit. The automatic proofs are still very
   quick (roughly 1 second on my machine for the entire file).

3) The tool gives no interesting output, which means that all proofs went
   through. You can also check this in the mentioned summary file.
