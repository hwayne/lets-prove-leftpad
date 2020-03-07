------------------------------ MODULE LeftPad ------------------------------
EXTENDS Naturals, Sequences, TLAPS

CONSTANTS alphabet, c, n, s

ASSUME ConstAssumption ==
  /\ c \in alphabet
  /\ n \in Nat
  /\ s \in Seq(alphabet)

max(x,y) == IF x>y THEN x ELSE y

(*
--algorithm LeftPad
variables
    output = s,
    
    \* local vars
    i = 0

define pad == max(n - Len(s), 0)
end define;

begin    
a:  while i<pad do
        output := <<c>> \o output;
        i := i + 1;
    end while
end algorithm
*)
\* BEGIN TRANSLATION PCal-00372dbce199f116a7ffb45377d629e8
VARIABLES output, i, pc

(* define statement *)
pad == max(n - Len(s), 0)


vars == << output, i, pc >>

Init == (* Global variables *)
        /\ output = s
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i<pad
           THEN /\ output' = <<c>> \o output
                /\ i' = i + 1
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << output, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION TLA-a0fc80ee85fca2fa827a5d462a7b566d

(***************************************************************************)
(* Specification for leftpad as given in the top-level readme in this      *)
(* repo:                                                                   *)
(*                                                                         *)
(* 1.  The length of the output is max(n, len(str))                        *)
(*                                                                         *)
(* 2.  The prefix of the output is padding characters and nothing but      *)
(* padding characters.                                                     *)
(*                                                                         *)
(* 3.  The suffix of the output is the original string.                    *)
(***************************************************************************)
Correct == pc="Done" => /\ Len(output) = max(n, Len(s))
                        /\ \E prefix \in Seq({c}) : output = prefix \o s
                    
TypeOK == /\ i \in Nat
          /\ pad \in Nat   \* pad is actually a constant expression, but we include it here for simplicity
          /\ pc \in {"a", "Done"}

(***************************************************************************)
(* This is the inductive invariant                                         *)
(***************************************************************************)
IInv == /\ \E prefix \in Seq({c}) : output = prefix \o s
        /\ Len(output) = Len(s) + i
        /\ 0 <= i /\ i <= pad
        /\ pc = "Done" => i >= pad

Inv == TypeOK /\ IInv
ISpec == Inv /\ [][Next]_vars

USE ConstAssumption

LEMMA Typing == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, pad, max
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, a, Terminating, vars, pad, max
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Invariant == Spec => []Correct
<1>1. Init /\ TypeOK => IInv
  <2>. Init => output = << >> \o s  BY DEF Init
  <2>. QED  BY Isa DEF Init, TypeOK, IInv
<1>2. Inv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>1. CASE a /\ i < pad
    <3>1. PICK pref \in Seq({c}) : output = pref \o s
      BY DEF Inv, IInv
    <3>2. <<c>> \o pref \in Seq({c}) /\ output' = (<<c>> \o pref) \o s
      BY <3>1, <2>1 DEF a
    <3>3. \E prefix \in Seq({c}) : output' = prefix \o s
      BY <3>2, Zenon
    <3>4. Len(output') = Len(output) + 1
      BY <2>1 DEF a
    <3>. QED  BY <3>3, <3>4, <2>1 DEF Inv, TypeOK, IInv, a
  <2>2. CASE a /\ ~(i < pad)
    BY <2>2 DEF Inv, TypeOK, IInv, a
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF Inv, IInv, vars
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF Next, Terminating
<1>3. Inv => Correct
  <2>. SUFFICES ASSUME Inv, pc = "Done" 
                PROVE  Len(output) = max(n, Len(s))
    BY DEF Inv, IInv, Correct
  <2>. i = IF n > Len(s) THEN n - Len(s) ELSE 0
    BY DEF Inv, TypeOK, IInv, pad, max
  <2>. QED  BY DEF Inv, TypeOK, IInv, max
<1>. QED  BY <1>1, <1>2, <1>3, Typing, PTL DEF Spec, Inv

=============================================================================
\* Modification History
\* Last modified Sat Feb 29 16:01:58 CET 2020 by merz
\* Created Sat Feb 29 12:28:29 CET 2020 by merz
