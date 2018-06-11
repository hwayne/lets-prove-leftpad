(** leftpad and its correctness.
    Solution to a challenge posed by twitter.com/hillelogram.
    Ezra Cooper, Apr 2018.
*)

Require Import Arith.
Require Import List.
Require Import Omega.

(* Require Import listkit. *)

(** [cutn] breaks a list into prefix, suffix at [n]. *)
Definition cutn A n (xs : list A) := (firstn n xs, skipn n xs).

(** [cutn n] is inverse of [(++)] when [n] equals the length of the first arg to [(++)]. *)
Lemma cutn_app:
  forall A n (xs ys : list A),
    n = length xs -> cutn A n (xs ++ ys) = (xs, ys).
Proof.
 induction n; destruct xs; simpl; easy||auto.
 intros.
 unfold cutn in *.
 simpl.
 lapply (IHn xs ys).
  congruence.
 omega.
Qed.

Hint Rewrite
     app_length
     repeat_length
  : list.

Hint Resolve
     repeat_spec
  : list.

(*  _      __ _                 _  *)
(* | |___ / _| |_ _ __  __ _ __| | *)
(* | / -_)  _|  _| '_ \/ _` / _` | *)
(* |_\___|_|  \__| .__/\__,_\__,_| *)
(* |_|                             *)

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

Definition allEqual A (xs : list A) y :=
  forall x, In x xs -> x = y.

Lemma correctness:
  forall padChar n s,
    length (leftpad padChar n s) = max n (length s) /\
    exists m,
      let (prefix, suffix) := cutn _ m (leftpad padChar n s) in
      allEqual _ prefix padChar /\
      suffix = s.
Proof.
 unfold leftpad, allEqual.
 split.
  autorewrite with list.
  apply minus_plus_max.
 eexists.
 rewrite cutn_app; eauto with list.
Qed.

(* This version posits a single function, cutn, which is an inverse to (++) *)
