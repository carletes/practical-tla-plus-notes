--------------------------------- MODULE in ---------------------------------
EXTENDS Integers, FiniteSets, TLC

(*--algorithm in

variables
    x \in 1..3;
    
begin
    assert x <= 2; 
end algorithm;-*)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..3
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x <= 2, "Failure of assertion at line 10, column 5.")
         /\ pc' = "Done"
         /\ x' = x

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Dec 26 10:47:15 GMT 2018 by carlos
\* Created Wed Dec 26 10:37:58 GMT 2018 by carlos
