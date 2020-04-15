-------------------------------- MODULE two --------------------------------
EXTENDS Integers

\*The variable 'i', always flips between zero and 1

VARIABLES i

TypeInvariant == i \in { 0, 1 }

Init == i = 0

Next == IF i = 0 THEN i' = 1
        ELSE i' = 0 

Spec == Init \/ [][Next]_<<>>

=============================================================================
THEOREM Spec => TypeInvariant
=============================================================================


=============================================================================
\* Modification History
\* Last modified Wed Apr 15 13:52:17 PDT 2020 by todd
\* Created Wed Apr 15 13:42:51 PDT 2020 by todd
