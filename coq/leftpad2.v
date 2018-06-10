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
  forall A n (c:A),
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
  n <= length xs ->
  firstn n (xs ++ ys) = firstn n xs.
Proof.
 induction n.
  simpl.
  auto.
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
    skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys.
Proof with (easy||auto).
 induction n; destruct xs; simpl...
Qed.

Lemma drop_everything:
  forall A (xs:list A) n,
    n >= length xs ->
    skipn n xs = nil.
Proof.
 induction xs; destruct n; simpl; intros; try (exfalso; omega); auto.
 apply IHxs.
 omega.
Qed.
  
Hint Rewrite firstn_repeat
     firstn_app
     skipn_app
     app_length
     repeat_length
  : list_lemmas.

Parameter char : Set.

Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.

Lemma correctness:
  forall c n s,
    length (leftpad c n s) = max n (length s) /\
    listall _ (fun x => x = c) (firstn (n - length s) (leftpad c n s)) /\
    skipn (n - length s) (leftpad c n s) = s.
Proof.
 unfold leftpad.
 firstorder (autorewrite with list_lemmas; auto).
    destruct (le_lt_dec n (length s)).
     rewrite max_r; omega.
    rewrite max_l; omega.
   apply listall_repeat.
  firstorder (autorewrite with list_lemmas; auto).
 firstorder (autorewrite with list_lemmas; auto).
 rewrite drop_everything.
 replace (n - length s - (n - length s)) with 0 by omega.
  solve [auto].
 autorewrite with list_lemmas.
 auto.
Qed.

(* This version wants the basic lemmas about firstn/skipn *)