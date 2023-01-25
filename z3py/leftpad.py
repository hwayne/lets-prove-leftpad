#!/usr/bin/env python3

# Alper Altuntas, 2023.

from z3 import *

Max = lambda x, y: If(x > y, x, y)


def leftpad(
        c = String('c'), 
        l = Int('l'),
        w = String('w'),
        do_prove = False):
    """
    Implements the leftpad operation by defining it as a
    constraint satisfaction problem (CSP) which is then
    solved using a z3py solver instance to obtain the
    resulting padded string.

    Parameters
    ----------
    c : String of length 1.
        The padding character.
    l : Int
        Total length of the padded string
    w : String
        The strings to be padded.

    Returns
    -------
    res: String
        padded string
    """

    if isinstance(c, str):
        assert len(c) == 1, "The length of c must be 1."

    # padding
    pad = String("pad")

    # result
    res = String("res")

    # The list of constraints that define the leftpad problem
    constraints = And(
        [
            # c is a character
            Length(c) == 1,
            # If word length is greater than l, pad is empty
            Implies(Length(w) >= l, pad == ""),
            # Else, pad consists of c only and len(pad) = l-len(w)
            Implies(
                Length(w) < l,
                And([InRe(pad, Star(Re(c))), Length(pad) == l - Length(w)]),
            ),
            # res is concatenation of pad and w:
            res == pad + w,
        ]
    )

    # Solve the constraint satisfaction problem that corresponds the leftpad operation
    s = Solver()
    s.add(constraints)
    s.check()

    if do_prove:
        postconditions = And(
            [
                # The length of the output is max(n, len(str))
                Length(res) == Max(l, Length(w)),
                # The prefix of the output is padding characters and nothing but padding characters
                Or(pad == "", InRe(pad, Star(Re(c)))),
                # The suffix of the output is the original string.
                SuffixOf(w, res),
            ]
        )

        prove(Implies(constraints, postconditions))

    return s.model()[res]


if __name__ == "__main__":
    print(leftpad("!", 5, "foo"))
    print(leftpad("!", 2, "foo"))
    leftpad(do_prove=True)
