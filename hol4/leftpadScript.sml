open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory rich_listTheory stringTheory;

val _ = new_theory "leftpad";

val leftpad_def = Define `
 leftpad c n str = REPLICATE (n - LENGTH str) c ++ str`;

val _ = EVAL ``leftpad (#"!") 5 "foo"``;

val _ = EVAL ``leftpad (#"!") 0 "foo"``;

(* Property 1: The length of the output is max(n, len(str)) *)

val prop_1 = Q.store_thm("prop_1",
 `!c n str. LENGTH (leftpad c n str) = MAX n (LENGTH str)`,
 rw [leftpad_def, MAX_DEF]);

(* Property 2: The prefix of the output is padding characters and nothing but padding characters *)

val TAKE_REPLICATE = Q.prove(
 `!n x. TAKE n (REPLICATE n x) = REPLICATE n x`,
 Induct \\ rw []);

val prop_2 = Q.store_thm("prop_2",
 `!c n str. TAKE (n - LENGTH str) (leftpad c n str) = REPLICATE (n - LENGTH str) c`,
 rw [leftpad_def, TAKE_APPEND, TAKE_REPLICATE]);

val prop_2_alt = Q.store_thm("prop_2_alt",
 `!c n str m. m < n - LENGTH str ==> (EL m (leftpad c n str) = c)`,
 rw [leftpad_def, EL_APPEND_EQN, EL_REPLICATE]);

(* Property 3: The suffix of the output is the original string *)

val prop_3 = Q.store_thm("prop_3",
 `!c n str. DROP (n - LENGTH str) (leftpad c n str) = str`,
 rw [leftpad_def, DROP_APPEND, DROP_REPLICATE]);

(* Alternative formulation of prop 2 and 3 based on cutn from the current Coq solution *)

val cutn_def = Define `
 cutn xs n = (TAKE n xs, DROP n xs)`;

val prop_cutn = Q.store_thm("prop_cutn",
 `!c n str. ?m.
   let (prefix, suffix) = cutn (leftpad c n str) m in
    (!x. MEM x prefix ==> (x = c)) /\ (suffix = str)`,
 rpt gen_tac \\ qexists_tac `n - LENGTH str` \\
 rw [cutn_def, prop_2, prop_3] \\ fs [MEM_EL, EL_REPLICATE]);

val _ = export_theory ();
