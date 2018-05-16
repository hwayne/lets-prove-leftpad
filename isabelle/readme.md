# [Isabelle](https://isabelle.in.tum.de)

## About Isabelle

Isabelle is primarily a theorem prover. It allows us to define things and
interactively prove properties about them. It can [generate executable
code](https://isabelle.in.tum.de/dist/Isabelle2017/doc/codegen.pdf) from
certain definitions but we don't use this functionality here.

## About the Proof

Isabelle's standard library and proof automation makes easy work of verifying
that the definition of `leftPad` satisfies the spec. To make it a bit more
interesting we go on to show that we didn't need the standard library's
`replicate` function (but we did need something equivalent) and also we show
that the spec for `leftPad` is _complete_ in the sense that it does not admit
any other functions.

## About Me

Hi, I'm [David Turner](https://twitter.com/DaveCTurner) and I've been proving
things in Isabelle for a very long time. By day I work for
[Elastic](https://elastic.co) where I get to prove things about distributed
systems such as [Elasticsearch](https://www.elastic.co/cloud).

## Tour of the proof

Isabelle's source format is a kind of LaTeX-like ASCII encoding of the source
you actually look at, which uses Unicode's mathematical symbols heavily. If you
[install Isabelle](https://isabelle.in.tum.de) you can load
[`Leftpad.thy`](Leftpad.thy) and play with the proof, but if you're just
interested in what it looks like then it's probably a better idea to read this.

### Part 1: Simply `leftPad`

What does it mean to be padded? A string can be split into two parts where the
first part is all padding and the second is the original string, which is
written like this.

    definition isPadded where "isPadded padChar unpadded padded
        ≡ ∃ n. set (take n padded) ⊆ { padChar } ∧ drop n padded = unpadded"

The star of the show is the `leftPad` function which is defined like this.

    definition leftPad where "leftPad padChar targetLength s
      ≡ replicate (targetLength - length s) padChar @ s"

This satisfies the spec as follows:

    lemma isPadded_leftPad: "isPadded padChar s (leftPad padChar targetLength s)"
      unfolding isPadded_def leftPad_def by (intro exI [where x = "targetLength - length s"], auto)

    lemma length_leftPad: "length (leftPad padChar targetLength s) = max targetLength (length s)"
      unfolding leftPad_def by auto

Mostly this proof is just definition unfolding and use of the `auto` tactic.
The only hard bit was to show that `∃ n. ...` holds in the definition of
`isPadded` we needed to give a specific value for `n`:

    intro exI [where x = "targetLength - length s"]

The proof automation doesn't find this on its own.

### Part 2: Avoiding `replicate`

But, hold on, we used `replicate` from the standard library which made this
very easy: there are a lot of facts about `replicate` already proven. Let's
assume we don't know about it: what facts do we need? How about these?

    locale replication =
      fixes abstract_replicate
      assumes length_replicate[simp]: "length (abstract_replicate n c) = n"
      assumes set_replicate[simp]: "set (abstract_replicate n c) = (if n = 0 then {} else {c})"

This creates a _locale_ which allows us to collect up some definitions and
facts together: here the `replication` locale has a function called
`abstract_replicate` with the listed properties, and we can then use this
function to define a more abstract version of `leftPad` and show that it, too,
satisfies the spec.

    context replication
    begin

    definition abstract_leftPad where "abstract_leftPad padChar targetLength s
      ≡ abstract_replicate (targetLength - length s) padChar @ s"

    lemma "isPadded padChar s (abstract_leftPad padChar targetLength s)"
      unfolding isPadded_def abstract_leftPad_def by (intro exI [where x = "targetLength - length s"], auto)

    lemma "length (abstract_leftPad padChar targetLength s) = max targetLength (length s)"
      unfolding abstract_leftPad_def by auto

    end

Of course we could have made an inconsistent set of assumptions in our locale
definition. We can check that we didn't by showing that there is an
_interpretation_: a way of instantiating the `abstract_replicate` variable that
is consistent. Of course we could just use the standard library's `replicate`
function:

    interpretation stdlib: replication replicate by (unfold_locales, auto)

However if we didn't know about that then we could also write our own quite
easily:

    fun myReplicate :: "nat ⇒ 'a ⇒ 'a list" where
      "myReplicate 0 c = []"
    | "myReplicate (Suc n) c = c # myReplicate n c"

To show that this satisfies the spec is also fairly straightforward for the
automation, as long as we tell it to start out by induction on `n` in each
case:

    interpretation mine: replication myReplicate proof
      fix n and c :: 'a
      show "length (myReplicate n c) = n" by (induct n, auto)
      show "set (myReplicate n c) = (if n = 0 then {} else {c})" by (induct n, auto)
    qed

### Part 3: There is only one `replicate`

In fact, the `length_replicate` and `set_replicate` facts are a complete
description of `replicate`, in the sense that `replicate` is the only function
that satisfies them:

    context replication
    begin

    lemma "abstract_replicate = replicate"

The proof is not completely trivial. The proof automation needs a little help
to find the right thing on which to do induction:

    proof (intro ext)
      fix n :: nat and c :: 'a
      {
        fix cs
        assume p: "length cs = n" "set cs = (if n = 0 then {} else {c})"
        hence "set cs = (if length cs = 0 then {} else {c})" by simp
        hence "cs = replicate (length cs) c"
        proof (induct cs)
          case Nil show ?case by simp
        next
          case (Cons c0 cs)
          from Cons.prems have "set cs = (if length cs = 0 then {} else {c})" by (cases cs, auto)
          with Cons.hyps have hyp: "cs = replicate (length cs) c" by simp
          with Cons.prems show ?case by simp
        qed
      }
      note p = this

      have "abstract_replicate n c = replicate (length (abstract_replicate n c)) c" by (intro p, simp_all)
      thus "abstract_replicate n c = replicate n c" by simp
    qed

    end

### Part 4: There is only one `leftPad`

Similarly, the spec for `leftPad` is a complete description of it, in the sense
that `leftPad` is the only function that satisfies it:

    lemma leftpad_unique:
      assumes isPadded_leftPad': "⋀padChar targetLength s. isPadded padChar s (leftPad' padChar targetLength s)"
      assumes length_leftPad': "⋀padChar targetLength s. length (leftPad' padChar targetLength s) = max targetLength (length s)"
      shows "leftPad' = leftPad"

The proof of this was surprisingly involved. It was interesting that it needed
to split on the case where the input string was empty or not: if nonempty then
the `n` in the `∃ n. ...` bit of the spec is exactly the amount of padding,
whereas if the input string is nonempty then any sufficiently-large `n` will
do: if `length xs ≤ n` then `take n xs = xs` and `drop n xs = []`.

    proof (intro ext)
      fix padChar :: 'a and targetLength s

      from isPadded_leftPad [of padChar] obtain n where n:
        "set (take n (leftPad padChar targetLength s)) ⊆ { padChar }"
        "drop n (leftPad padChar targetLength s) = s"
        unfolding isPadded_def by blast

      from isPadded_leftPad' obtain n' where n':
        "set (take n' (leftPad' padChar targetLength s)) ⊆ { padChar }"
        "drop n' (leftPad' padChar targetLength s) = s"
        unfolding isPadded_def by blast

      {
        fix xs xs'
        assume "set xs ⊆ { padChar }" "set xs' ⊆ { padChar }" "length xs = length xs'"
        hence "xs = xs'"
        proof (induct xs arbitrary: xs')
          case Nil thus ?case by simp
        next
          case (Cons x xs xxs')
          from Cons obtain x' xs' where xxs': "xxs' = x' # xs'" by (cases xxs', auto)
          with Cons show ?case by auto
        qed
      }
      note padding_eq = this

      have append_cong: "⋀ws xs ys zs. ws = ys ⟹ xs = zs ⟹ ws @ xs = ys @ zs" by simp

      have "leftPad' padChar targetLength s = take n' (leftPad' padChar targetLength s) @ drop n' (leftPad' padChar targetLength s)" by simp
      also have "... = take n (leftPad padChar targetLength s) @ drop n (leftPad padChar targetLength s)"
      proof (intro append_cong)
        from n n' show "drop n' (leftPad' padChar targetLength s) = drop n (leftPad padChar targetLength s)" by simp

        have "length (take n' (leftPad' padChar targetLength s)) = length (take n (leftPad padChar targetLength s))"
        proof (cases s)
          case Cons

          from n have "length s = length (drop n (leftPad padChar targetLength s))" by simp
          also have "... = length (leftPad padChar targetLength s) - n" by simp
          also from length_leftPad [of padChar] have "... = max targetLength (length s) - n" by simp
          finally have n_eq: "n = max targetLength (length s) - length s" using Cons by auto

          from n' have "length s = length (drop n' (leftPad' padChar targetLength s))" by simp
          also have "... = length (leftPad' padChar targetLength s) - n'" by simp
          also from length_leftPad' have "... = max targetLength (length s) - n'" by simp
          finally have n'_eq: "n' = max targetLength (length s) - length s" using Cons by auto

          show ?thesis by (simp add: length_leftPad length_leftPad' n_eq n'_eq)
        next
          case Nil                        
          with n n' length_leftPad [of padChar] length_leftPad'
          show ?thesis by auto
        qed
        thus "take n' (leftPad' padChar targetLength s) = take n (leftPad padChar targetLength s)"
          by (intro padding_eq n n')
      qed
      also have "... = leftPad padChar targetLength s" by simp

      finally show "leftPad' padChar targetLength s = leftPad padChar targetLength s" .
    qed

    end
