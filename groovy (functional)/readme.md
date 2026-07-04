# [Groovy (Functional, groovy-verify)](https://github.com/paulk-asert/groovy-verify)

A functional proof of leftpad in [Apache Groovy](https://groovy.apache.org/) — no loops, no
mutation, recursion + induction — verified at **compile time** by
[groovy-verify](https://github.com/paulk-asert/groovy-verify) (a static type-checking extension
that discharges contract annotations with Z3 during compilation). No online demo yet; the proof is
pinned in groovy-verify's test corpus (the `P211 structural leftpad` group) and reproduces with
`./gradlew verify`.

## About Groovy and groovy-verify

See the sibling [imperative entry](../groovy/readme.md) for the tool description. The relevant
extra here: a method's own `@Ensures` is assumed at its recursive call sites — sound because
`@Decreases` proves the recursion terminates — which is precisely proof by induction. Void methods
whose only job is to carry an `@Ensures` act as lemmas/theorems: call one, and its (proved) fact
enters your proof context. That gives Groovy the spec-function / proof-function structure this
repo's Verus entry uses, with plain methods.

## About the proof

The recursion prepends one pad character to the recursive result, decreasing `n`
(`pad + leftpad(pad, n - 1, s)`), and its specification is **structural** rather than index-wise:

```groovy
result == pads(pad, n - s.length()) + s     // when s.length() < n
```

where `pads(pad, k)` is a recursive padding builder (`k` copies of the pad character). This single
equality is properties 2 and 3 in one stroke — the output *is* the padding block followed by the
original string, so the prefix is nothing but pad characters and the suffix is exactly `s`, by
construction rather than by index arithmetic. The identity case (`s.length() >= n ==> result == s`)
covers the no-padding side.

Property 1 (the length) is **derived**, Verus-style: `padsLen` proves `|pads(pad, k)| == k` by
induction on `k`, and `lengthTheorem` then concludes `|leftpad(pad, n, s)| == n` from the
structural postcondition plus that lemma (length-of-concatenation is a theorem of the SMT
sequence theory the verifier models strings with, so no axiom is needed).

Two mechanical details formal-methods readers may enjoy: the induction hypothesis is just the
method's own `@Ensures` at the recursive call, justified by the `@Decreases({ n - s.length() })`
measure; and the recursion is deliberately shaped to prepend to the *result* — the
accumulator-passing variant (`leftpad(pad, n, pad + s)`, the shape of this repo's functional Dafny
entry) states the same structural equality only via a commutation lemma
(`pad + pads(k) == pads(k) + pad`), which the result-prepending shape never needs.

