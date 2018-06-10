(** leftpad and its correctness.
    Solution to a challenge posed by twitter.com/hillelogram.
    Ezra Cooper, Apr 2018.
*)

Require Import Arith.
Require Import List.
Require Import Omega.
 
Hint Rewrite
     app_length
     repeat_length
  : list_lemmas.

Parameter char : Set.

Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.

Lemma minus_plus_max:
  forall m n, m - n + n = max m n.
Proof.
 intros.
 destruct (le_lt_dec m n).
  rewrite max_r; omega.
 rewrite max_l; omega.
Qed.

Lemma correctness:
  forall c n s,
    length (leftpad c n s) = max n (length s) /\
    exists m, leftpad c n s = repeat c m ++ s.
Proof.
 unfold leftpad.
 firstorder (autorewrite with list_lemmas; auto).
 apply minus_plus_max.
 exists (n - length s).
 auto.
Qed.

