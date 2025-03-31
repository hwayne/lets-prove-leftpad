[VeriFast for C](https://github.com/verifast/verifast)
==============

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

### The specification

The precondition asserts ownership of a null-terminated string at `s` whose list of characters is `cs`, as well as, if the length of the string is less than `n`, `n - length(cs)` bytes of (possibly uninitialized) memory at `s + length(cs) + 1`.

`&*&` denotes separating conjunction; `?cs` introduces a new ghost variable `cs` bound to the (symbolic) value found at the corresponding argument position of the predicate.

The postcondition asserts ownership of a null-terminated string at `s` whose length is at least `n`, which has `cs` as a suffix, and whose remaining bytes are all equal to `c`.

By including the `terminates;` clause, the specification asserts total correctness.

Links to relevant definitions:
- [Predicate `string`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/prelude.h#L1017)
- [Mathematical function `length`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/list.gh#L35)
- [Mathematical function `all_eq`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/list.gh#L262)
- [Mathematical function `take`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/list.gh#L117)
- [Mathematical function `drop`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/list.gh#L140)

### The proof

The specifications for `strlen`, `memmove`, and `memset` are in the annotated version of [`string.h`](https://github.com/verifast/verifast/blob/master/bin/string.h) that ships with VeriFast.

The annotations are mostly lemma calls. The calls of
[`string_limits`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/prelude.h#L1052)
and
[`chars__limits`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/prelude.h#L378)
help VeriFast see that `s + p` is valid pointer arithmetic. `all_eq_mem` and
`chars_string_join` are custom lemmas proven earlier in the file. These lemmas
are recursive; VeriFast notices that they perform induction on the structure of
[`list`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/list.gh#L19)
value `xs` and the derivation of the
[`chars`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/prelude.h#L357)
predicate, respectively. The `open` and `close` ghost commands unfold and fold the predicate definition, respectively. The calls of lemmas [`take_append`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/listex.gh#L18) and [`drop_append`](https://github.com/verifast/verifast/blob/339351d28411d3bcb926d318576820288752aeaf/bin/listex.gh#L116) defined in `listex.gh` complete the proof of the postcondition.

### How to run

Download the latest [`nightly build`](https://github.com/verifast/verifast/releases/tag/nightly) for your platform, extract the archive to anywhere on your computer (on Macs, first [remove the quarantine bit](https://github.com/verifast/verifast?tab=readme-ov-file#binaries)), and run `path/to/verifast/bin/vfide leftpad.c`. In the IDE, click the Play toolbar button to verify the program.