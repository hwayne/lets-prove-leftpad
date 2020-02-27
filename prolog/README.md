# Prolog

[Prolog](https://www.swi-prolog.org/) is a logic programming language---you define the relations in your program, then query the system to see.

# Try Online

The solution can be viewed [here](https://swish.swi-prolog.org/p/Leftpad.pl) online.
Example:

```prolog
?- leftpad(0, 5, [1,2,3], Padded).
Padded = [0, 0, 1, 2, 3] .
```

# About This Solution

A verified solution can be "wrong" for only two reasons:
1. The specification is "wrong".
2. The underlying tools have bugs in them.

However, this program meets the same two criteria: it's "implementation" **is** the specification of left pad, just written in Prolog.
Put another way, there is no implementation, only the specification.
So as long the translation of the specification into Prolog is correct, and Prolog itself (SWI-Prolog, in this case) works, then this program must do what the specification says.

# About Me

My name is [Reed Oei](http://reedoei.com), I'm a student in Math and Computer Science at [UIUC](https://illinois.edu/), and I'm interested in theorem provers and programming languages.

