# [Groovy (groovy-verify)](https://github.com/paulk-asert/groovy-verify)

An imperative proof of leftpad in [Apache Groovy](https://groovy.apache.org/), verified at
**compile time** by [groovy-verify](https://github.com/paulk-asert/groovy-verify) — a static
type-checking extension that discharges design-by-contract annotations with the Z3 SMT solver
while ordinary compilation runs. There is no online demo yet; to reproduce, clone groovy-verify
and run `./gradlew verify` — this exact proof is pinned in its test corpus (the
`P207 sequential loops` group), and a broken invariant or postcondition fails compilation with a
concrete counterexample.

## About Groovy and groovy-verify

Groovy is a JVM language — a close superset of Java with optional static typing. Its
design-by-contract library ([groovy-contracts](https://groovy-lang.org/)) checks `@Requires` /
`@Ensures` / loop `@Invariant` / `@Decreases` annotations **at runtime**. groovy-verify reuses
those same stock annotations and proves them **statically**: it plugs into `@TypeChecked` (Groovy's
static type checker is user-extensible), translates method bodies and contracts to SMT, and reports
a failed proof as a compile error carrying a counterexample (Dafny-style), or an honest
"skipped — outside the supported fragment" warning when it cannot model something. So the same
annotations are checked twice: proved at compile time, and enforced at runtime as a second rung.

## About the proof

The specification on `leftpad` is the challenge's three properties, stated directly over the
result array: the length is `max(n, len(s))`, every slot of the prefix equals the pad character,
and the suffix is `s` element-for-element.

The implementation is the classic two-loop form (fill the padding, then copy the string), and the
proof is classic Hoare logic: each loop carries an `@Invariant` (established on entry, preserved by
the body, conjoined with the negated guard on exit) and a `@Decreases` termination measure. The
detail worth noticing is the second loop's invariant: it **restates** the first segment's fact
(`(0..<pad).every { r[it] == c }`) — the second loop writes the same array, so anything the first
loop established must be carried through the second loop's own invariant to survive. That is
exactly the discipline JML's `maintaining` clauses impose in this repo's Java/OpenJML entry, which
this proof is deliberately shaped after (Java is largely a syntactic subset of Groovy, so the two
entries are line-for-line comparable).

The quantified specification clauses (`(0..<k).every { ... }`) are ordinary Groovy — runnable
closures over ranges — which the verifier reads as bounded universal quantifiers.

