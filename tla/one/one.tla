-------------------------------- MODULE one --------------------------------
EXTENDS Naturals

\*The variable 'i', once set in the 'Init' step, never changes.

CONSTANT N
ASSUME N \in Nat
VARIABLES i

TypeInvariant == i \in N

Init == i = N

Next == i' = i

Spec == Init \/ [][Next]_<<i>>

=============================================================================
THEOREM Spec => TypeInvariant
=============================================================================
\* Modification History
\* Last modified Wed Apr 15 13:39:22 PDT 2020 by todd
\* Created Wed Apr 15 13:14:55 PDT 2020 by todd
