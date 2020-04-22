------------------------------ MODULE logical_clock  ------------------------------
EXTENDS TLC
PT == INSTANCE PT
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

\* ---------------------------------------------------------------------------
\* Constants
\* ---------------------------------------------------------------------------
CONSTANT Proc                   \* processors
CONSTANT MaxValue               \* max value for any clock 
                                \* (limit state space)
CONSTANT MaxSent                \* max number of sent items per process
                                \* (limit state space)
CONSTANT Solution               \* which solution to try (see readme.md)

ASSUME Solution \in { 1 , 2, 3 }
ASSUME Cardinality(Proc) > 0    \* we need at least one proc

\* ---------------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------------
VARIABLES 
    \* Variables intrinsic to the clock
    clock,                      \* each clock has it's current value 
    inbox,                      \* each clock process has a msg inbox (queue)
    
    \* Auxilary variables for use in reasoning about the clock
    read,                       \* messages that the process has read from inbox 
    sent,                       \* each clock process has a history of sent changes
    clock_h                     \* each clock has a history of value changes


vars  == << inbox, read, sent, clock, clock_h >>

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------
MyReduceSeq(op(_,_), set, acc) ==
    IF set = <<>>
    THEN acc
    ELSE PT!ReduceSeq(op, set, acc)

\* ---------------------------------------------------------------------------
\* Constraints
\* 
\* These are artificial constraints to limit the state space of the specs.
\* This decreases the runtime of the spec, but may limit the modeler such
\* that it misses interesting paths.
\* ---------------------------------------------------------------------------

ClockConstraint ==
    \A p \in Proc : clock[p] <= MaxValue

MaxSentConstraint ==
    \A p \in Proc : Len(sent[p]) <= MaxSent


\* ---------------------------------------------------------------------------
\* Safety checks (INVARIANTS)
\* ---------------------------------------------------------------------------


\* ---------------------------------------------------------------------------
\* Behaviours
\* ---------------------------------------------------------------------------

Init == 
    /\ inbox    = [p \in Proc |-> <<>>]
    /\ sent     = [p \in Proc |-> <<>>]
    /\ read     = [p \in Proc |-> <<>>]
    /\ clock    = [p \in Proc |-> 0]
    /\ clock_h  = [p \in Proc |-> <<>>]

EmptyOrNaturalSeq(s) == 
    Len(SelectSeq(s, LAMBDA x: ~(x \in Nat))) = 0

TypeInvariant ==
    /\ \A p \in Proc :
        /\ clock[p] \in Nat
        /\ EmptyOrNaturalSeq(inbox[p])
        /\ EmptyOrNaturalSeq(sent[p])
        /\ EmptyOrNaturalSeq(read[p])
        /\ EmptyOrNaturalSeq(clock_h[p])


MaxInClockHist(p)     == MyReduceSeq(PT!Max, clock_h[p], 0)
MaxInSent(p)          == MyReduceSeq(PT!Max, sent[p], 0)
MaxInRead(p)          == MyReduceSeq(PT!Max, read[p], 0)
MaxInInbox(p)         == MyReduceSeq(PT!Max, inbox[p], 0)

Coherence ==
    /\ \A p \in Proc :
        \* A clock is always current
        /\ clock[p] = MaxInClockHist(p)
        \* A clock is never behind what it sent
        /\ clock[p] >= MaxInSent(p)
        \* A clock always increases in value
        /\ IF clock_h[p] = <<>> 
            THEN 
                TRUE
            ELSE 
                IF Len(clock_h[p]) = 1 
                    THEN 
                        TRUE 
                    ELSE 
                        \A i \in 1..(Len(clock_h[p])-1): clock_h[p][i] < clock_h[p][i + 1]

(*
Solution 1

This is the incorrect interpretation of the algorithm:

    * increment the `s` process's clock
    * send the incremented `s` clock to the target process's inbox

Later, the target process will read it's inbox and set it's clock to the 
max of the inbox values and it's current value, and then add 1.
*)

WorkerIncrementSAndThenSendToT(self) ==
    /\ Cardinality(Proc) > 1
    /\ LET 
            other_clocks == {x \in Proc : x # self}
            next_clock == clock[self] + 1
        IN  
            /\ clock' = [clock EXCEPT ![self] = next_clock]
            /\ clock_h'= [clock_h EXCEPT ![self] = Append(@, next_clock)]
            /\ \E target \in other_clocks : 
                    /\ inbox' = [inbox EXCEPT ![target] = Append(@, next_clock)]
                    /\ sent' = [sent EXCEPT ![self] = Append(@, next_clock)]
            /\ UNCHANGED <<read>>

(*
Solution 2

IMO this is the correct interpretation of the algorithm:

    * send `s` process's clock to target process
    * `s` does not increment it's own clock as part of the send action

Later, the target process will read it's inbox the same as above.
*)
WorkerSendSToTAndThenIncrement(self) ==
    /\ Cardinality(Proc) > 1
    /\ LET 
            other_clocks == {x \in Proc : x # self}
        IN  
            /\ \E target \in other_clocks : 
                    /\ inbox' = [inbox EXCEPT ![target] = Append(@, clock[self])]
                    /\ sent' = [sent EXCEPT ![self] = Append(@, clock[self])]
            /\ UNCHANGED <<read, clock, clock_h>>

WorkerReadInbox(self) ==
    /\ inbox[self] # <<>>
    /\ LET 
            inbox_max == PT!ReduceSeq(PT!Max, inbox[self], 0)
        IN 
            /\ IF inbox_max > clock[self]
                THEN
                    /\ clock' = [clock EXCEPT ![self] = inbox_max + 1]
                    /\ clock_h' = [clock_h EXCEPT ![self] = Append(@, inbox_max + 1)]
                    /\ UNCHANGED << sent>>
                ELSE
                    /\ UNCHANGED << sent, clock, clock_h>>
            /\ read' = [read EXCEPT ![self] = @ \o inbox[self]]
            /\ inbox' = [inbox EXCEPT ![self] = <<>>]

\* Internal increment steps are required if number of processors
\* is 1, otherwise the spec deadlocks.
WorkerInternal(self) ==
    LET 
        next_clock == clock[self] + 1
    IN
        /\ clock' = [clock EXCEPT ![self] = next_clock]
        /\ clock_h' = [clock_h EXCEPT ![self] = Append(@, next_clock)]
        /\ UNCHANGED <<inbox, read, sent>>



Worker(self) == 
    CASE Solution = 1 -> 
        \/ WorkerIncrementSAndThenSendToT(self)
        \/ WorkerReadInbox(self)
        \/ WorkerInternal(self)
    [] Solution = 2 -> 
        \/ WorkerSendSToTAndThenIncrement(self)
        \/ WorkerReadInbox(self)
        \/ WorkerInternal(self)
    [] Solution = 3 -> 
        \/ WorkerSendSToTAndThenIncrement(self)
        \/ WorkerReadInbox(self)

Next == \E self \in Proc: Worker(self)

Spec == /\ Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
