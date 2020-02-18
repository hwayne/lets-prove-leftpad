# ACL2

## About ACL2

ACL2 is an untyped functional programming language with a first order
logic describing its semantics, along with a theorem prover that
facilitates reasoning in that logic.

The ACL2 theorem prover is at its heart a rewriting system.  When you
prove a theorem in ACL2, it is usually stored as a rewrite rule.  For
example, if you prove that p(X, Y) => f(X, g(Y)) = h(X, Y), then ACL2
will remember that whenever it sees something matching f(X, g(Y)), it
should try to prove p(X, Y), and if it succeeds, then it should
rewrite f(X, g(Y)) to h(X, Y).  Note that this means that proving that
A = B is different from proving that B = A!

The ACL2 language is based on a mostly pure subset of Common Lisp, and
in fact the ACL2 interpreter translates ACL2 function and constant
definitions directly into Common Lisp definitions which usually look
very similar to the original ACL2 definitions.  This closeness to
Common Lisp means that ACL2 code can be written to directly benefit
from the high performance of Common Lisp compilers, which has made
ACL2 popular in some industrial applications including hardware
verification.  Scalability and performance are important design
considerations for the ACL2 authors.

You can learn more about ACL2 at [the ACL2 website][ACL2 website].

## About this leftpad

Since ACL2 is a functional language, a natural way to write leftpad is
to use recursion.

We start with a naive definition for leftpad which works on lists of
characters instead of strings (in ACL2, as in Common Lisp, the string
type is different from a list of characters, unlike in C, Haskell, or
various other languages).

After proving Hillel's three properties on this recursive definition,
we then define a more efficient version of the function which
calculates the padding amount in advance, builds the entire padding
string, and then concatenates it to the original string with Common
Lisp's native `concatenate` function.

Finally, we use ACL2's [MBE][MBE] ("must-be-equal") feature to define
a function whose logical definition acts like the original recursive
function but whose runtime behavior is similar to the more efficient
version, which we are allowed to do only after proving that the two
functions are equivalent under certain conditions.  Features like MBE
can be useful for writing "real software" in ACL2 that has to run fast
while also being tractable to reason about.

[ACL2 website]: http://www.cs.utexas.edu/users/moore/acl2/
[MBE]: http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=ACL2____MBE
