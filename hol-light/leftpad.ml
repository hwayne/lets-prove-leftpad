(* Define the leftpad function on lists using primitives
   from the standard library. The subtraction here operates
   on values of type 'num' and saturates at zero rather
   than returning negative numbers. *)
let LEFTPAD = new_definition
  `LEFTPAD n x l = APPEND (REPLICATE (n - LENGTH l) x) l`;;

(* For the spec it'll be convenient to have a DROP
   function that drops the first few elements of a
   list. *)
let DROP = new_recursive_definition num_RECURSION
  `(DROP 0 (l:A list) = l) /\
   (DROP (SUC n) l = DROP n (TL l))`;;

(* A lemma relating DROP and APPEND *)
let DROP_APPEND = prove
 (`!(l1:A list) l2. DROP (LENGTH l1) (APPEND l1 l2) = l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; DROP; TL]);;

(* The stdlib is missing one simple lemma about
   REPLICATE *)
let EL_REPLICATE = prove
 (`!n i (x:A). i < n ==> EL i (REPLICATE n x) = x`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; REPEAT GEN_TAC] THEN
  STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[REPLICATE; EL; HD; TL; LT_SUC]);;

(* We prove that (LEFTPAD n x l) always returns a list of
   at last n elements. We also prove that if the input list
   l has length less than n, then the first 'n - LENGTH l'
   elements are x, and the rest (defined using DROP) is the
   input list l. *)
let LEFTPAD_CORRECT = prove
 (`!n (x:A) l.
   LENGTH (LEFTPAD n x l) >= n /\
   (!i. i < n - LENGTH l ==> EL i (LEFTPAD n x l) = x) /\
   DROP (n - LENGTH l) (LEFTPAD n x l) = l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LEFTPAD] THEN
  REPEAT CONJ_TAC THENL 
  (* -- Property 1 -- *)
  [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC ;
  (* -- Property 2 -- *)
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[EL_APPEND; LENGTH_REPLICATE] THEN
   POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC EL_REPLICATE ;
  (* -- Property 3 -- *)
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM (
     ISPECL [`n - LENGTH (l:A list)`; `x:A`]
     LENGTH_REPLICATE)] THEN
   MATCH_ACCEPT_TAC DROP_APPEND]);;
