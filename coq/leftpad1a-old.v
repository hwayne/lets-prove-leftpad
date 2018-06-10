(** leftpad and its correctness.
    Solution to a challenge posed by twitter.com/hillelogram.
    Ezra Cooper, Apr 2018.
*)

Require Import Arith.
Require Import List.
Require Import Omega.

(* Require Import listkit. *)


(** All elements of a list have a property. *)
Fixpoint listall A P (xs:list A) :=
  match xs with
      nil => True
    | (x::xs) => P x /\ listall _ P xs
  end.

Definition cutn A n (xs : list A) := (firstn n xs, skipn n xs).

(** [cutn] breaks a list into prefix, suffix at [n]. *)
(** [listall] says that all elements of a list satisfy a predicate.
    We use [listall (fun x => x = pad)] which assert that they all have the same value. *)

(** If we conjure copies of a value, all the elements of the list are equal to that value. *)
Lemma listall_repeat :
  forall A c n,
    listall A (fun x => x = c) (repeat c n).
Proof with auto.
 induction n; simpl...
Qed.

Lemma cutn_app:
  forall A n (xs ys : list A),
    n = length xs -> cutn A n (xs ++ ys) = (xs, ys).
Proof.
 induction n; destruct xs; simpl; easy||auto.
 intros.
 unfold cutn in *.
 simpl.
 cut ((firstn n (xs ++ ys), skipn n (xs ++ ys)) = (xs, ys)).
  congruence.
 apply IHn.
 omega.
Qed.
                                        
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
  forall padChar n s,
    length (leftpad padChar n s) = max n (length s) /\
    let (prefix, suffix) := (cutn _ (n - length s) (leftpad padChar n s)) in
      listall _ (fun x => x = padChar) prefix /\
      suffix = s.
Proof.
 unfold leftpad.
 split.
  autorewrite with list_lemmas.
  apply minus_plus_max.
 rewrite cutn_app.
  split.
   apply listall_repeat.
  auto.
 autorewrite with list_lemmas; auto.
Qed.
