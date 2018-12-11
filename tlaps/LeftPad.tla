------------------------------ MODULE LeftPad ------------------------------
EXTENDS Naturals, Sequences, TLAPS

CONSTANTS alphabet

max(x,y) == IF x>y THEN x ELSE y

(*
--algorithm LeftPad
variables
    \* inputs
    c \in alphabet,
    n \in Nat,
    s \in Seq(alphabet),
    
    output = s,
    
    \* local vars
    pad = max(n - Len(s), 0),
    i = 0
begin    
a:  while i<pad do
        output := <<c>> \o output;
        i := i + 1;
    end while
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES c, n, s, output, pad, i, pc

vars == << c, n, s, output, pad, i, pc >>

Init == (* Global variables *)
        /\ c \in alphabet
        /\ n \in Nat
        /\ s \in Seq(alphabet)
        /\ output = s
        /\ pad = max(n - Len(s), 0)
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i<pad
           THEN /\ output' = <<c>> \o output
                /\ i' = i + 1
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << output, i >>
     /\ UNCHANGED << c, n, s, pad >>

Next == a
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

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
                    
TypeOK == /\ c \in alphabet
          /\ n \in Nat
          /\ s \in Seq(alphabet)
          /\ output \in Seq(alphabet)
          /\ pad \in Nat
          /\ i \in Nat
          /\ pc \in {"a", "Done"}

(***************************************************************************)
(* This is the inductive invariant                                         *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \E prefix \in Seq({c}) : output = prefix \o s
       /\ Len(output) = Len(s) \/ Len(output) <= n
       /\ Len(output) = Len(s) + i 
       /\ pad = max(n - Len(s), 0)
       /\ i>=0
       /\ Correct

ISpec == Inv /\ [][Next]_vars

THEOREM Spec=>[]Correct
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2> USE DEF Init
  <2>1. TypeOK
    BY DEF TypeOK,max
  <2>2. \E prefix \in Seq({c}) : output = prefix \o s
    <3>1. output = << >> \o s
        OBVIOUS
    <3>2. << >> \in Seq({c})
        BY DEF Seq
    <3>3. QED BY <3>1, <3>2
  <2>3. Len(output) = Len(s) \/ Len(output) <= n
    OBVIOUS
  <2>4. Len(output) = Len(s) + i
    OBVIOUS
  <2>5. pad = max(n - Len(s), 0)
    OBVIOUS
  <2>6. i>=0
    OBVIOUS
  <2>7. Correct
    BY DEF Correct
  <2>8. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE a
    <3>1. TypeOK'
        BY <2>1 DEF a,TypeOK
    <3>2. (\E prefix \in Seq({c}) : output = prefix \o s)'
        <4>1. IF i<pad THEN output' = <<c>> \o output ELSE UNCHANGED output
            BY <2>1 DEF a
        <4>2. CASE i<pad
            <5>1. \E prefix \in Seq({c}) : output = prefix \o s
                OBVIOUS
            <5>2. \E prefix \in Seq({c}) : <<c>> \o output = <<c>> \o prefix \o s
                OBVIOUS
            <5>3. \A p \in Seq({c}) : <<c>> \o p \in Seq({c})
                OBVIOUS
            <5>4. \E prefix \in Seq({c}) : <<c>> \o output = prefix \o s
                BY <5>2,<5>3
            <5>5. output' = <<c>> \o output
                BY <4>1,<4>2
            <5>6. \E prefix \in Seq({c}) : output' = prefix \o s
                BY <5>4,<5>5
            <5>7. s' = s
                BY <2>1 DEF a
            <5>8. \E prefix \in Seq({c}) : output' = prefix \o s'
                BY <5>6,<5>7
            <5>9. c' = c
                BY <2>1 DEF a
            <5>10. \E prefix \in Seq({c'}) : (output = prefix \o s)'
                BY <5>8,<5>9
            <5>11. QED
                BY <5>10
        <4>3. CASE ~(i<pad)
            BY <2>1,<4>1,<4>3 DEF a
        <4>4. QED BY <4>1,<4>2,<4>3
    <3>3. (Len(output) = Len(s) \/ Len(output) <= n)'
        BY <2>1 DEF a,Inv,TypeOK,Next,vars,max
    <3>4. (Len(output) = Len(s) + i)'
        BY <2>1 DEF Inv,a,TypeOK
    <3>5. (i>=0)'
        BY <2>1 DEF a, TypeOK
    <3>6. (pad = max(n - Len(s), 0))'
        BY <2>1 DEF a,TypeOK
    <3>7. Correct'
        BY <2>1,<3>2 DEF a,TypeOK,max,Inv,Correct
    <3>8. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Inv
  <2>2. CASE pc = "Done" /\ UNCHANGED vars
      BY <2>2 DEF vars,TypeOK,Correct,Inv
  <2>3. CASE UNCHANGED vars
    <3> USE DEF vars
    <3>1. TypeOK'
        BY <2>3 DEF TypeOK
    <3>2. (\E prefix \in Seq({c}) : output = prefix \o s)'
        BY <2>3
    <3>3. (Len(output) = Len(s) \/ Len(output) <= n)'
        BY <2>3
    <3>4. (Len(output) = Len(s) + i)'
        BY <2>3
    <3>5. (pad = max(n - Len(s), 0))'
        BY <2>3
    <3>6. (i>=0)'
        BY <2>3
    <3>7. Correct'
        BY <2>3 DEF Correct
    <3>8. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Inv
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. Inv => Correct
    BY DEF Inv
<1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec 


=============================================================================
\* Modification History
\* Last modified Tue Dec 11 13:27:11 EST 2018 by lhochstein
\* Created Wed Dec 05 17:06:03 CET 2018 by lhochstein
