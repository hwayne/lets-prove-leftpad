# [Python](https://www.python.org)

# About Python

From [The Python Tutorial](https://docs.python.org/3/tutorial/index.html):

> Python is an easy to learn, powerful programming language. It has efficient
> high-level data structures and a simple but effective approach to
> object-oriented programming. Python’s elegant syntax and dynamic typing,
> together with its interpreted nature, make it an ideal language for scripting
> and rapid application development in many areas on most platforms.

# About this proof

This implementation uses the [Deal](https://deal.readthedocs.io) library and the
[mypy](https://mypy.readthedocs.io) static type checker.  It is roughly based on
the already existing
[Java solution](https://github.com/hwayne/lets-prove-leftpad/tree/master/java).

Deal supports design by contract (DbC) and relies on the
[Hypothesis](https://hypothesis.readthedocs.io) library to execute bounded
property checks.

All these Python dependencies can be installed by running

    pip3 install -r requirements.txt

It is recommended that you create and activate a Python 3 virtualenv first.

A `GNUmakefile` is provided mostly for documentation purposes; it contains all
commands that must be executed in order to run the proofs.
