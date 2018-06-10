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

(** firstn returns the first n elements of a list. *)
(** skipn returns what follows after the first n elements of a list. *)
(** [listall] says that all elements of a list satisfy a predicate.
    We use [listall (fun x => x = pad)] which assert that they all have the same value. *)

(** After conjuring up n copies of an element, taking n of them is a no-op. *)
Lemma firstn_repeat:
  forall A (n:nat) (c:A),
    firstn n (repeat c n) = repeat c n.
Proof with auto.
 induction n; simpl...
 intro c.
 rewrite IHn...
Qed.

(** Taking n elements of a concatentation, when n is less than the
    length of the first concatenand, gives just n elements of that concatenand. *)
Lemma firstn_app:
  forall A n (xs ys : list A),
  n = length xs ->
  firstn n (xs ++ ys) = xs.
Proof.
 induction n.
  simpl.
  destruct xs; auto.
  simpl; discriminate.
  destruct xs.
  easy.
 simpl.
 intros.
 rewrite IHn.
  auto.
 omega.
Qed.

(** If we conjure copies of a value, all the elements of the list are equal to that value. *)
Lemma listall_repeat :
  forall A c n,
    listall A (fun x => x = c) (repeat c n).
Proof with auto.
 induction n; simpl...
Qed.

(** Dropping the first n elements of a concatenation, when n is the
    length of the first concatenand, gives just the second concatenand. *)
Lemma skipn_app:
  forall A n (xs ys : list A),
    n = length xs ->
    skipn n (xs ++ ys) = ys.
Proof with (easy||auto).
 induction n; destruct xs; simpl...
Qed.
  
Hint Rewrite
     firstn_repeat
     firstn_app
     skipn_app
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
    listall _ (fun x => x = padChar) (firstn (n - length s) (leftpad padChar n s)) /\
    skipn (n - length s) (leftpad padChar n s) = s.
Proof.
 unfold leftpad.
 firstorder (autorewrite with list_lemmas; auto).
    apply minus_plus_max.
   apply listall_repeat.
(* final two goals are actually the same... :-/ *)
   firstorder (autorewrite with list_lemmas; auto).
 firstorder (autorewrite with list_lemmas; auto).
Qed.

(* This version views firstn/skipn as being some kind of inverse of
app, so the lemmas only deal with exact cuts at the division between
xs ++ ys. *)