# Python

## About Python

You've probably heard of [Python](https://www.python.org/)... though it's not a language
usually associated with formally verified code!

## About This Solution

The `leftpad` function lists pre- and post-conditions in the docstring, which
are verified by symbolic execution with [CrossHair](https://github.com/pschanely/CrossHair)
(and the Z3 backend).

I wrote the function body as a loop purely to avoid having the code as a
near-duplicate of the spec, though that would actually be more efficient
at runtime!

The spec can be [verified online here](https://crosshair-web.org/?crosshair=0.1&python=3.8&gist=026709425e8e73cbd513d5f4e6884a39),
including by breaking the implementation - try replacing `<` with `<=`, for example!

## Why I love CrossHair

It's integrated into Python!  The syntax for pre- and post-conditions is drawn from
a (long-deferred) [Python Enhancement Proposal](https://www.python.org/dev/peps/pep-0316/),
and the way it leverages `assert` statements creates a lovely synergy with property-based
testing tools like [Hypothesis](https://hypothesis.readthedocs.io/).
It supports partial specs, right down to `post: True` to mean "no unexpected exceptions".

And the barrier to entry is *so freaking low* that anyone can use it.

## About me

I'm a core developer of [Hypothesis](https://hypothesis.readthedocs.io/), and trying
to improve the reliability of the Python ecosystem - especially foundational projects
like CPython, Numpy, and Pandas where bugs can have serious impacts on many people's
lives.  More about me at [`zhd.dev`](https://zhd.dev/).
