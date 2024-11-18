------------------------------ MODULE Leftpad ------------------------------
EXTENDS Integers, Sequences, TLAPS
Max(i, j) == IF i < j THEN j ELSE i
Leftpad(c, n, s) == [i \in 1..Max(n, Len(s)) |-> IF i <= n - Len(s) THEN c ELSE s[i - Max(0, n - Len(s))]]
THEOREM LeftpadCorrect ==
  \A Char : \A c \in Char, n \in Nat, s \in Seq(Char) :
    /\ Len(Leftpad(c, n, s)) = Max(n, Len(s))
    /\ \A i \in 1..Max(0, n - Len(s)) : Leftpad(c, n, s)[i] = c
    /\ \A i \in DOMAIN s : Leftpad(c, n, s)[Max(0, n - Len(s)) + i] = s[i]
BY DEF Leftpad, Max
=============================================================================
