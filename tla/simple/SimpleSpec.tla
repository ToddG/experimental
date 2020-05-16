----------------------------- MODULE SimpleSpec -----------------------------
EXTENDS Integers
VARIABLES i, pc   

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"  
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle" 
        /\ i' = i + 1
        /\ pc' = "done"  
           
Next == Pick \/ Add1


=============================================================================
\* Modification History
\* Last modified Wed Apr 15 11:35:04 PDT 2020 by todd
\* Created Wed Apr 15 11:34:42 PDT 2020 by todd
