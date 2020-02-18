# [SMT-LIB 2.0](http://smtlib.cs.uiowa.edu/)

This is a proof of Leftpad using the SMT-LIB language, which is used as an input format to the [Z3 theorem prover](https://github.com/Z3Prover/z3).

Since the leftpad function can be represented as a "pure" function that maps input strings to output strings, we can represent the input arguments to the function and the output argument as symbolic values, and describe the relationship between those values. That is, we define the set of constraints that must hold between the input string and the padded, output string as assertions in the SMT language. We can then ask the Z3 solver to find a model that satisfies these constraints. If we add assertions that give concrete values to the input arguments (e.g. see the "test cases" section in the code), then the solver gives us a model that represents the computation of the output string i.e. the value of the `out` string in the model will represent the application of the leftpad function to the input parameters we specified. Since we want to prove properties about leftpad in general, though, we leave the input parameters abstract and then define the correctness properties that we want to prove. To prove these properties, we assert their negation and see if Z3 can find a satisfying model. If it does, this means there is some model that satisfies both the rules of the leftpad function and also violates a correctness property. If Z3 returns `unsat`, we take that as proof that the property holds for our leftpad function in general, which is what our goal is. The properties we check are named in the code as the `length-property`, the `prefix-property`, and the `suffix-property`, and correspond, respectively, to the [3 specification properties](https://github.com/hwayne/lets-prove-leftpad/tree/6c428a10dc71cc486b6007146f58633877c97a18#why-are-we-proving-leftpad) listed in the main README.

 ## Running the Verification Step

 You can try to run the code in Z3 [here](https://rise4fun.com/Z3/HrVRz), but I encountered timeout issues when running in the web browser. For me, it was more reliable to download a Z3 binary from the [releases](https://github.com/Z3Prover/z3/releases) page and run locally with the following command:

 ```
z3 -smt2 leftpad.smt
 ```

 This produced the following output on a 2015 Macbook in under a second:

 ```
"check length-property."
unsat
(error "line 57 column 10: model is not available")
"check prefix-property."
unsat
(error "line 67 column 10: model is not available")
"check suffix-property."
unsat
(error "line 76 column 10: model is not available")
"test cases"
sat
(model 
  (define-fun s () String
    "he")
  (define-fun c () String
    "p")
  (define-fun prefix () String
    "ppp")
  (define-fun out () String
    "ppphe")
  (define-fun n () Int
    5)
)
sat
(model 
  (define-fun s () String
    "hello")
  (define-fun c () String
    "p")
  (define-fun prefix () String
    "")
  (define-fun out () String
    "hello")
  (define-fun n () Int
    3)
)
sat
(model 
  (define-fun s () String
    "hello")
  (define-fun c () String
    "p")
  (define-fun prefix () String
    "")
  (define-fun out () String
    "hello")
  (define-fun n () Int
    5)
)

 ```

## Checking our Work

As a sanity check, we can artificially "break" the definition of leftpad to make sure that the correctness property verification steps actually fail. We can break each of the 3 correctness properties independently.

If we alter the "main computational step" of leftpad to be:

```smt
(assert (= out (str.++ prefix (str.++ "w" s))))
```

then Z3 produces a model that violates the `length-property`:

```
"check length-property."
sat
(model
  (define-fun s () String
    "")
  (define-fun c () String
    "\x00")
  (define-fun prefix () String
    "")
  (define-fun out () String
    "w")
  (define-fun n () Int
    (- 1))
)
```

This is the only property that is violated, since we have not changed the prefix, and have not changed the suffix, but have inserted an extra character that alters the overall length of the output string. 

If we alter the main computational step instead to be:

```smt
(assert (= out (str.++ prefix (str.replace s "a" "b"))))
```

we can see Z3 produce a model violating the `suffix-property` alone:

```
"check suffix-property."
sat
(model
  (define-fun s () String
    "a")
  (define-fun c () String
    "\x00")
  (define-fun prefix () String
    "\x00")
  (define-fun out () String
    "\x00b")
  (define-fun n () Int
    2)
)
```

 This is because we have simply replaced some characters in the expected suffix, without changing the length of the output string or altering the padding prefix. 


Finally, we can alter this assertion:

```smt
(assert (is-repeated-char prefix c))
```

which defines the characters of the prefix padding string to:

```smt
(assert (is-repeated-char prefix "w"))
```

and Z3 produces a model violating the `prefix-property`:

```
"check prefix-property."
sat
(model
  (define-fun s () String
    "\x00")
  (define-fun c () String
    "\x00")
  (define-fun prefix () String
    "w")
  (define-fun out () String
    "w\x00")
  (define-fun n () Int
    2)
)
```

 This gives us more confidence that our correctness property checks are verifying what we think they are. By using Z3 there is not much "proof" work to be done here, other than writing down the correctness properties. Once we've done that, verification is a mostly automated task.