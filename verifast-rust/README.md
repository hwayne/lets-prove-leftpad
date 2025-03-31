[VeriFast for Rust](https://github.com/verifast/verifast)
===================

About VeriFast
--------------

VeriFast is a tool for the modular formal verification of single-threaded and
multithreaded C, Java, and Rust programs. It takes as input a source code file
that includes function preconditions and postconditions, loop invariants, and
other annotations in the form of special comments, and, typically after a
matter of seconds, reports either "0 errors found" or a symbolic execution
trace leading to a verification failure. It performs per-function/method
symbolic execution, using a separation logic representation of memory, and
using an SMT solver to reason about data values.

About the Proof
---------------

### The code

With this version of `leftpad`, our goal is to illustrate VeriFast's support for
verifying purely unsafe Rust code. Since it's not Rust-like to assume that
strings are null-terminated, this `leftpad` function takes the length of the
given string as an argument `ns`. It returns the length of the resulting string.

### The specification

The precondition asserts ownership of the array of bytes at `s` of length `ns`, whose elements are `cs`, as well as, if `ns` is less than `n`, `n - ns` bytes of (possibly uninitialized) memory at `s + ns`.

`&*&` denotes separating conjunction; `?cs` introduces a new ghost variable `cs` bound to the (symbolic) value found at the corresponding argument position of the predicate.

The postcondition asserts ownership of an array of padding bytes at `s` followed by the bytes that were originally at `s`.

By including the `on_unwind_ens false;` clause, the specification asserts that this function never
unwinds. (Unwinding is Rust's analogue of throwing an exception.)

By including the `terminates;` clause, the specification asserts total correctness.

Links to relevant definitions:
- [Mathematical function `repeat`](https://github.com/verifast/verifast/blob/3bb34d95980421c76c359b77cc9ee22a6fea5283/bin/rust/listex.rsspec#L29)
- [Mathematical datatype `nat`](https://github.com/verifast/verifast/blob/master/bin/rust/nat.rsspec)

### The proof

The specifications for `copy` and `write_bytes` are in file [`bin/rust/std/lib.rsspec`](https://github.com/verifast/verifast/blob/3bb34d95980421c76c359b77cc9ee22a6fea5283/bin/rust/std/lib.rsspec#L103) which contains specifications for some of the Rust standard library APIs.

The call of lemma [`div_rem_nonneg`](https://github.com/verifast/verifast/blob/3bb34d95980421c76c359b77cc9ee22a6fea5283/bin/rust/prelude_core.rsspec#L59) is necessary for VeriFast to see that pointer `s` is properly aligned for type `u8`.

### How to run

Download the latest [`nightly build`](https://github.com/verifast/verifast/releases/tag/nightly) for your platform, extract the archive to anywhere on your computer (on Macs, first [remove the quarantine bit](https://github.com/verifast/verifast?tab=readme-ov-file#binaries)), and run `path/to/verifast/bin/vfide leftpad.rs`. In the IDE, click the Play toolbar button to verify the program.

### Addendum: using `leftpad` in safe code

See [here](https://github.com/verifast/verifast/blob/master/tests/rust/purely_unsafe/leftpad.rs) to see
a proof of a safe function `leftpad_vec` that takes a `Vec<u8>` instead of a pointer, and that calls
the unsafe `leftpad` function verified here. The proof of `leftpad_vec`, however, exposes two as-yet
missing features of VeriFast. Firstly, VeriFast does not yet support injecting ghost code onto unwind
paths; as a result, for now, `leftpad_vec` can only be verified while ignoring unwind paths. This is because
if the `reserve` call unwinds, `Vec_to_own` needs to be called. Secondly, VeriFast does not yet support
specifying functional correctness properties of safe functions; for now, VeriFast verifies only their semantic
well-typedness.