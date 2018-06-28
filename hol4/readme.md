# HOL4

HOL4 is a proof assistant, similar to e.g. Coq or Isabelle/HOL. You can find more information at https://hol-theorem-prover.org.

We start the proof development by defining a `leftpad` function:

```
val leftpad_def = Define `
 leftpad c n str = REPLICATE (n - LENGTH str) c ++ str`;
```

The functions `REPLICATE` and `LENGTH` are from the HOL4 standard library. The function `leftpad` is defined in terms of (non-negative) natural numbers which can be arbitrarily large, and strings represented as lists. The notation `++` is from the standard library also, and means list append.

For example, ` EVAL ``leftpad (#"!") 5 "foo"`` ` will give us the theorem

```
leftpad #"!" 5 "foo" = "!!foo",
```

and ` EVAL ``leftpad (#"!") 0 "foo"`` ` will give us the theorem

```
leftpad #"!" 0 "foo" = "foo".
```

## Property 1: The length of the output is max(n, len(str))

The first property is simple enough for the HOL rewriter, here invoked by the tactic `rw`, to be able to solve it (`MAX` is from the standard library):

```
val prop_1 = Q.store_thm("prop_1",
 `!c n str. LENGTH (leftpad c n str) = MAX n (LENGTH str)`,
 rw [leftpad_def, MAX_DEF]);
```

The second line is the theorem statement, and the third line is the single tactic needed to prove the statement. The tactic `rw` carries around an implicit set of common theorems from the standard library, so common theorems do not need to be mentioned explicitly.

## Property 2: The prefix of the output is padding characters and nothing but padding characters

For the second property one should note that strings can have multiple prefixes, so "[t]he prefix" is ambiguous... but let's assume the prefix of length (n - len(str)) is intended.

We need the following simple lemma, which is not included in the standard library, to prove the property (`TAKE` is, again, from the standard library):

```
val TAKE_REPLICATE = Q.prove(
 `!n x. TAKE n (REPLICATE n x) = REPLICATE n x`,
 Induct \\ rw []);
```

The proof is by induction on `n` (`Induct`), and by combining the two involved tactic by `\\`, `rw` is run on the two generated subgoals, which are solved immediately.

Using this lemma and a theorem from the standard library we can prove the second property using the rewriter again:

```
val prop_2 = Q.store_thm("prop_2",
 `!c n str. TAKE (n - LENGTH str) (leftpad c n str) = REPLICATE (n - LENGTH str) c`,
 rw [leftpad_def, TAKE_APPEND, TAKE_REPLICATE]);
```

The correspondence between one's formal theorem statement and the property it is intended to capture is (almost) always problematic, and an alternative formalization could be (`EL` is, again, from the standard library, and the name is an abbreviation for "element"):

```
val prop_2_alt = Q.store_thm("prop_2_alt",
 `!c n str m. m < n - LENGTH str ==> (EL m (leftpad c n str) = c)`,
 rw [leftpad_def, EL_APPEND_EQN, EL_REPLICATE]);
```

## Property 3: The suffix of the output is the original string

For the third property we have a similar ambiguity problem as for the second property (strings can have multiple suffixes...). Ignoring this, we can use the rewriter again to prove our property (`DROP` is, again, from the standard library):

```
val prop_3 = Q.store_thm("prop_3",
 `!c n str. DROP (n - LENGTH str) (leftpad c n str) = str`,
 rw [leftpad_def, DROP_APPEND, DROP_REPLICATE]);
```

## Alternative formulation of property 2 and 3 based on `cutn` from the current Coq solution

One can also formalize the second and third property using `cutn` from the current Coq solution:

```
val cutn_def = Define `
 cutn xs n = (TAKE n xs, DROP n xs)`;

val prop_cutn = Q.store_thm("prop_cutn",
 `!c n str. ?m.
   let (prefix, suffix) = cutn (leftpad c n str) m in
	(!x. MEM x prefix ==> (x = c)) /\ (suffix = str)`,
 rpt gen_tac \\ qexists_tac `n - LENGTH str` \\
 rw [cutn_def, prop_2, prop_3] \\ fs [MEM_EL, EL_REPLICATE]);
```
