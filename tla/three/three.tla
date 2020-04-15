------------------------------- MODULE three -------------------------------
EXTENDS Integers

\*The variable 'i', always increments to 9 and then starts back at 0.

VARIABLES i

TypeInvariant == i \in {0..9}

Init == i = 0

Next == 
    IF i < 9 
    THEN i' = i + 1
    ELSE i' = 0 

Spec == Init \/ [][Next]_<<i>>

=============================================================================
THEOREM Spec => TypeInvariant
=============================================================================
\* Modification History
\* Last modified Wed Apr 15 14:12:10 PDT 2020 by todd
\* Created Wed Apr 15 13:54:25 PDT 2020 by todd
