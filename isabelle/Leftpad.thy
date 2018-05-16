theory Leftpad
  imports Main
begin

(* What does it mean to be padded? A string can be split into two parts where the first part
   is all padding and the second is the original string: *)

definition isPadded where "isPadded padChar unpadded padded
    \<equiv> \<exists> n. set (take n padded) \<subseteq> { padChar } \<and> drop n padded = unpadded"

(* The star of the show is the `leftPad` function ... *)

definition leftPad where "leftPad padChar targetLength s
  \<equiv> replicate (targetLength - length s) padChar @ s"

(* ... which satisfies the spec: *)

lemma isPadded_leftPad: "isPadded padChar s (leftPad padChar targetLength s)"
  unfolding isPadded_def leftPad_def by (intro exI [where x = "targetLength - length s"], auto)

lemma length_leftPad: "length (leftPad padChar targetLength s) = max targetLength (length s)"
  unfolding leftPad_def by auto



(* But, hold on, we used `replicate` from the standard library which made this very easy:
   there are a lot of facts about `replicate` already proven. Let's assume we don't know about it:
   what facts do we need? How about these: *)

locale replication =
  fixes abstract_replicate
  assumes length_replicate[simp]: "length (abstract_replicate n c) = n"
  assumes set_replicate[simp]: "set (abstract_replicate n c) = (if n = 0 then {} else {c})"

(* This works: *)

context replication
begin

definition abstract_leftPad where "abstract_leftPad padChar targetLength s
  \<equiv> abstract_replicate (targetLength - length s) padChar @ s"

lemma "isPadded padChar s (abstract_leftPad padChar targetLength s)"
  unfolding isPadded_def abstract_leftPad_def by (intro exI [where x = "targetLength - length s"], auto)

lemma "length (abstract_leftPad padChar targetLength s) = max targetLength (length s)"
  unfolding abstract_leftPad_def by auto

end

(* Of course it's important that the real `replicate` function satisfies this spec: *)

interpretation stdlib: replication replicate by (unfold_locales, auto)

(* However, if we didn't know about it then we could write our own quite easily: *)

fun myReplicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "myReplicate 0 c = []"
| "myReplicate (Suc n) c = c # myReplicate n c"

(* ... and show it satisfies the spec too: *)

interpretation mine: replication myReplicate proof
  fix n and c :: 'a
  show "length (myReplicate n c) = n" by (induct n, auto)
  show "set (myReplicate n c) = (if n = 0 then {} else {c})" by (induct n, auto)
qed

(* In fact, the `length_replicate` and `set_replicate` functions are a complete description of
   `replicate`, in the sense that `replicate` is the only function that satisfies them: *)

context replication
begin

lemma "abstract_replicate = replicate"
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

(* Similarly, the spec for `leftPad` is a complete description of it, in the sense that `leftPad`
   is the only function that satisfies it: *)

lemma leftpad_unique:
  assumes isPadded_leftPad': "\<And>padChar targetLength s. isPadded padChar s (leftPad' padChar targetLength s)"
  assumes length_leftPad': "\<And>padChar targetLength s. length (leftPad' padChar targetLength s) = max targetLength (length s)"
  shows "leftPad' = leftPad"
proof (intro ext)
  fix padChar :: 'a and targetLength s

  from isPadded_leftPad [of padChar] obtain n where n:
    "set (take n (leftPad padChar targetLength s)) \<subseteq> { padChar }"
    "drop n (leftPad padChar targetLength s) = s"
    unfolding isPadded_def by blast

  from isPadded_leftPad' obtain n' where n':
    "set (take n' (leftPad' padChar targetLength s)) \<subseteq> { padChar }"
    "drop n' (leftPad' padChar targetLength s) = s"
    unfolding isPadded_def by blast

  {
    fix xs xs'
    assume "set xs \<subseteq> { padChar }" "set xs' \<subseteq> { padChar }" "length xs = length xs'"
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

  have append_cong: "\<And>ws xs ys zs. ws = ys \<Longrightarrow> xs = zs \<Longrightarrow> ws @ xs = ys @ zs" by simp

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
