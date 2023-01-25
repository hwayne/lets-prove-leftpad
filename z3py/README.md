# About Z3

Z3 is a widely used Satisfiability Modulo Theories (SMT) solver. It has APIs available
in multiple languages including the Python API (z3py) used in this example. The link
to the Z3 tutorial written by the core developers:
https://theory.stanford.edu/~nikolaj/programmingz3.html

Z3 is open-source and available at: https://github.com/Z3Prover/z3

# The CSP approach

In this example, I view the leftpad operation as a constraint satisfaction problem (CSP)
where I describe the implementation of the operation as a list of logical constraints.
To do so, I use the String and Regex theories readily available in Z3. I then instantiate
a Z3 solver instance and instruct it to generate a satisfying *model* that contains the 
string resulting from the leftpad operation.

For the proof, I use the z3py `prove` method which tries to prove the given claim by
by showing the negation is unsatisfiable. As for the claim, it is simply a logical
implication where antecedent is the list of constraints corresponding to the leftpad
operation and the consequent is the list of the three postconditions.

# Running the script

First, install the `z3-solver` Python library: 

```
$ pip install z3-solver
```

Then, simply run the `leftpad.py` script as follows:

```
./leftpad.py 
```

This will execute the following function calls:
```
    print(leftpad("!", 5, "foo"))
    print(leftpad("!", 2, "foo"))
    leftpad(do_prove=True)
```

And should lead to the following output:
```
"!!foo"
"foo"
proved
```

# About Me

I am a software engineer at the National Center for Atmospheric Research. As a scientific
software developer, I have a strong passion to devise and apply formal verification
techniques in scientific and high-performance computing applications.

Alper Altuntas, 2023.
https://github.com/alperaltuntas