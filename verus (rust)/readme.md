# [Verus](https://verus-lang.github.io/verus/guide/)

## About Verus

Verus is a verification framework built on top of Rust. It draws inspiration from tools like Dafny and translates specifications into the Z3 SMT solver. Verus provides extensions to the Rust language through new specification-friendly types like `int` and `Seq` for reasoning about numerical properties and collections. Macros like `requires` and `ensures` are defined to assist with writing proofs. Verus is flexible because it allows you to write a standalone proof or apply proofs to existing libraries.

## About the Proof

This folder contains two different implementations of the leftpad proof. 

#### Main Proof - `leftpad_spec.rs`

`leftpad_spec.rs` demonstrates how to link a more efficient "executable" leftpad implementation to a simplified, proven leftpad implementation. Verus has three types of functions: `spec` for describing properties, `proof` for proving properties a satisfied, and `exec` functions that can be compiled and run. `spec` and `proof` functions are "ghost" code that get evaluated and then removed during compilation. The full proof is wrapped in the `verus! {}` macro, which lets us use the Rust extensions defined in Verus to verify the code.

We start with a trivial recursive implementation of `leftpad` using a `spec` function. The base case is to return the string `s` if its length is already greater than or equal to `n`. Else, prepend the character `c` to the result of the recursive call with `n -> n - 1`. Additionally, `spec` functions are defined for each property we want to prove:
- `spec fn result_has_correct_length(result: Seq<char>, n: nat, s: Seq<char>);`
- `spec fn prefix_is_only_padded_characters(c: char, n: nat, s: Seq<char>, result: Seq<char>);`
- `spec fn suffix_is_original_string(c: char, n: nat, s: Seq<char>, result: Seq<char>);`

The `proof` function `leftpad_proof` verifies through induction that for a given input `(c, n, s)`, all of the above properties hold for each recursive step down to the base case. 

Finally, we use `exec` to define an iterative implementation of leftpad. This function `ensures` that its output is equivalent to the output of the recursive implementation. It also defines an `invariant` asserting that in each iterative step, the accumulated result is again equivalent to the output from the recursive implementation.

Here is a link with this proof in the Verus playground: https://play.verus-lang.org/?version=stable&mode=basic&edition=2021&gist=d89424e82a2dd03df7b35aa81eeb2c16

#### Extra Proof - `leftpad_impl.rs`

`leftpad_impl.rs` is an example of how you can apply Verus to existing libraries. Instead of wrapping everything in the `verus! {}` macro, we can take a regular Rust function and annotate it with `#[verus_spec]` to enable verification. This leftpad implementation once again uses the iterative approach but proves the 3 properties directly instead of linking it to a separate function. 



## Running the proof

The Verus installation guide is here: https://github.com/verus-lang/verus/blob/main/INSTALL.md. 

The code block below shows how to use Verus from the command line. Note: In this example, `verus` has been defined as an alias to the actual binary installed above. 


```
➜  verus (rust) git:(master) ✗ verus src/leftpad_spec.rs
verification results:: 5 verified, 0 errors

➜  verus (rust) git:(master) ✗ verus --compile src/leftpad_spec.rs 
verification results:: 5 verified, 0 errors

➜  verus (rust) git:(master) ✗ ./leftpad_spec 

Input: c=!, n=0, s=['f', 'o', 'o']
Output: result=['f', 'o', 'o']


Input: c=!, n=3, s=['f', 'o', 'o']
Output: result=['f', 'o', 'o']


Input: c=!, n=4, s=['f', 'o', 'o']
Output: result=['!', 'f', 'o', 'o']
```