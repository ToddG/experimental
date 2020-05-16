-------------------------------- MODULE four --------------------------------
EXTENDS Naturals

\* The N players are passing a socker ball back and forth. One of the
\* players always has the ball.

CONSTANT N  \* number of players
ASSUME N \in Nat \ {0}

VARIABLES 
    i \* player_with_ball
   
    
TypeInvariant == 
    /\ N \in Nat \ {0}
    /\ i \in { 0..N-1 }

Players == { 0..N-1 }
OpenPlayer == CHOOSE p \in Players : p != i

Init == 
    i = CHOOSE p \in Players

Next == 
    i' = OpenPlayer

Spec == 
    Init \/ [][Next]_<<i>>

=============================================================================
THEOREM Spec => TypeInvariant
=============================================================================

=============================================================================
\* Modification History
\* Last modified Wed Apr 15 14:41:54 PDT 2020 by todd
\* Created Wed Apr 15 14:23:20 PDT 2020 by todd
