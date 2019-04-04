module Leftpad

open FStar.Char
open FStar.Seq

(* Helper *)
let max a b = if a > b then a else b

(* Definition *)
let leftpad (c:char) (n:nat) (s:seq char) : seq char =
  let pad = max (n - length s) 0 in
  append (create pad c) s

(* Spec and verification *)
let leftpad_correct (c:char) (n:nat) (s:seq char) =

  let r = leftpad c n s in

  (* Two abbreviations to make conditions below more legible *)
  let ssz = length s in
  let pad = max (n - ssz) 0 in

  (* These are all statically checked for validity over all inputs *)
  let _ = assert (length r = max n ssz) in
  let _ = assert (forall (i:nat). i < n - ssz ==> index r i = c) in
  let _ = assert (forall (i:nat). i < ssz ==> index r (pad + i) = index s i) in
()
