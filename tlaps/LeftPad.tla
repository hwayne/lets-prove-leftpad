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
        <4>1. IF i<pad THEN output' = <<c>> \o output ELSE UNCHANGED output
            BY <2>1 DEF a
        <4>2. CASE i<pad
            BY <2>1,<4>1,<4>2 DEF Inv,TypeOK,a,Next,vars,max
        <4>3. CASE ~(i<pad)
            <5>1. output' = output
                BY <4>3 DEF Next,a, vars
            <5>2. s' = s
                BY <2>1 DEF a
            <5>3. i>=pad
                BY <4>3 DEF TypeOK
            <5>4. pad = max(n - Len(s), 0)
                OBVIOUS
            <5>5. CASE pad = n - Len(s)
                BY <5>1,<5>2 DEF Inv,TypeOK,Next,a,vars
            <5>6. CASE pad = 0
                <6>1. i=0
                    BY <5>6 DEF Inv,TypeOK,max
                <6>2. Len(output) = Len(s)
                    BY <6>1 DEF Inv
                <6>3. (Len(output) = Len(s))'
                    BY <6>2,<5>1,<5>2
                <6>4. QED
                    BY <6>3
            <5>7. QED
                BY <5>3,<5>4,<5>5,<5>6 DEF max
        <4>4. QED
            BY <4>1,<4>2,<4>3
    <3>4. (Len(output) = Len(s) + i)'
        <4>1. CASE i<pad
            <5>1. Len(output) = Len(s) + i
                BY DEF Inv
            <5>2. Len(output') = Len(output) + 1
                BY <2>1,<4>1 DEF a,TypeOK
            <5>3. s' = s
                BY <2>1 DEF a
            <5>4. i' = i + 1
                BY <2>1,<4>1 DEF a
            <5>5. Len(output') = Len(s) + i + 1
                BY <5>1,<5>2
            <5>6. Len(output') = Len(s) + i'
                BY <5>4,<5>5
            <5>7. (Len(output) = Len(s) + i) '
                BY <5>3,<5>6
            <5> QED BY <5>7
        <4>2. CASE ~(i<pad)
            <5>1. s'=s
                BY <2>1 DEF a
            <5>2. i'=i
                BY <4>2,<2>1 DEF a
            <5>3. output'=output
                BY <4>2,<2>1 DEF a
            <5>4. Len(output) = Len(s) + i
                BY DEF Inv
            <5>5. Len(output') = Len(s') + i'
                BY <5>1,<5>2,<5>3,<5>4
            <5> QED
                BY <5>5 
        <4>3. QED
            BY <4>1,<4>2
    <3>5. (i>=0)'
        BY <2>1 DEF a, TypeOK
    <3>6. (pad = max(n - Len(s), 0))'
        <4>1. pad'=pad
            BY <2>1 DEF a
        <4>2. n'=n
            BY <2>1 DEF a
        <4>3. s'=s
            BY <2>1 DEF a
        <4> QED
            BY <4>1,<4>2,<4>3 DEF TypeOK
    <3>7. Correct'
        <4> USE DEF Correct
        <4>1. CASE (pc = "Done")'
            <5>1. (Len(output) = max(n, Len(s)))'
                <6>1. ~(i<pad)
                    BY <4>1,<2>1 DEF a
                <6>2. output'=output
                    BY <6>1,<2>1 DEF a
                <6>3. Len(output)' = Len(output)
                    BY <6>2
                <6>4. n'=n
                    BY <6>1,<2>1 DEF a
                <6>5. s'=s
                    BY <6>1,<2>1 DEF a
                <6>6. Len(s)' = Len(s)
                    BY <6>5
                <6>7. (Len(output) = max(n, Len(s)))' = (Len(output) = max(n, Len(s)))
                    BY <6>3,<6>4,<6>6
                <6>8. CASE pad=0
                    <7>1. n - Len(s) <= 0
                        <8> SUFFICES ASSUME ~(n - Len(s) <= 0)
                                     PROVE FALSE
                            OBVIOUS
                        <8>1. n - Len(s) > 0
                            BY DEF TypeOK
                        <8>2 pad = n - Len(s)
                            BY <8>1 DEF max,Inv
                        <8>3. pad > 0
                            BY <8>2
                        <8> QED
                            BY <6>8,<8>3
                    <7>2. Len(s) >= n
                        BY <7>1 DEF TypeOK
                    <7>3. Len(output) = Len(s)
                        <8>1. Len(output) = Len(s) + i
                            BY DEF Inv
                        <8>2. i = 0
                            <9> USE DEF TypeOK
                            <9>1. i = Len(output) - Len(s)
                                BY DEF Inv
                            <9>2. Len(output) = Len(s) \/ Len(output) <= n
                                BY DEF Inv
                            <9>3. CASE Len(output) = Len(s)
                                <10> QED 
                                    BY <9>1, <9>3 
                            <9>4. CASE Len(output) <= n
                                <10>0. Len(s)+i<=n
                                    BY <9>4 DEF Inv
                                <10>1. i <= n - Len(s)
                                    BY <10>0
                                <10>2. n - Len(s) <= 0
                                    BY <7>1
                                <10>3. i>=0
                                    BY DEF Inv
                                <10>. QED
                                    BY <10>1,<10>2,<10>3
                            <9> QED
                                BY <9>2,<9>3,<9>4
                        <8> QED
                            BY <8>1,<8>2 DEF TypeOK
                    <7>4. Len(output) = max(n, Len(s))
                        <8>1. CASE Len(s)>n 
                            BY <7>3,<8>1 DEF max,TypeOK
                        <8>2. CASE Len(s)=n 
                            BY <8>2 DEF max,TypeOK
                        <8> QED
                            BY <7>2,<8>1,<8>2 DEF TypeOK
                    <7> QED
                        BY <7>4,<6>7
                <6>9. CASE ~(pad=0)
                    BY <2>1,<4>1 DEF Inv,a,max,TypeOK
                <6> QED
                    BY <6>8,<6>9

            <5>2. (\E prefix \in Seq({c}) : output = prefix \o s)'
                BY <3>2
            <5> QED
                BY <5>1,<5>2
        <4>2. CASE ~(pc = "Done")'
            BY <4>2
        <4> QED
            BY <4>1,<4>2
    <3>8. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Inv
  <2>2. CASE pc = "Done" /\ UNCHANGED vars
    <3> USE DEF vars
    <3>1. TypeOK'
        BY <2>2 DEF TypeOK
    <3>2. (\E prefix \in Seq({c}) : output = prefix \o s)'
        BY <2>2
    <3>3. (Len(output) = Len(s) \/ Len(output) <= n)'
        BY <2>2
    <3>4. (Len(output) = Len(s) + i)'
        BY <2>2
    <3>5. (pad = max(n - Len(s), 0))'
        BY <2>2
    <3>6. (i>=0)'
        BY <2>2
    <3>7. Correct'
        BY <2>2 DEF Correct
    <3>8. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Inv
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
\* Last modified Tue Dec 11 13:11:06 EST 2018 by lhochstein
\* Created Wed Dec 05 17:06:03 CET 2018 by lhochstein
