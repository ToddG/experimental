\* don't reset the inbox after read
\* only put max values in the inbox 
------------------------------ MODULE logical_clock3  ------------------------------
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
CONSTANT MaxClockValue          \* max value for any process's clock
CONSTANT MaxInboxLength         \* max depth for any process's inbox
ASSUME Cardinality(Proc) > 0    \* we need at least one proc

\* ---------------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------------
VARIABLES 
    clock,                      \* each clock has it's current value 
    inbox                       \* each clock process has a single inbox value

vars  == << clock, inbox >>

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

ClockValueConstraint ==
    \A p \in Proc : clock[p] <= MaxClockValue

Constraints ==
    /\ ClockValueConstraint

\* ---------------------------------------------------------------------------
\* ActionConstraints
\* ---------------------------------------------------------------------------

ActionConstraints == TRUE

\* ---------------------------------------------------------------------------
\* Behaviours
\* ---------------------------------------------------------------------------

Init == 
    /\ inbox    = [p \in Proc |-> 0]
    /\ clock    = [p \in Proc |-> 0]

EmptyOrNaturalSeq(s) == 
    Len(SelectSeq(s, LAMBDA x: ~(x \in Nat))) = 0

TypeInvariant ==
    /\ \A p \in Proc :
        /\ clock[p] \in Nat
        /\ inbox[p] \in Nat

Invariants ==
    /\ TypeInvariant

WorkerSend(self) ==
    /\ Cardinality(Proc) > 1
    /\ LET 
            other_clocks == {x \in Proc : x # self}
        IN  
            /\ \E target \in other_clocks : 
                    /\ inbox' = [inbox EXCEPT ![target] = PT!Max(@, clock[self])]
            /\ UNCHANGED << clock >>

WorkerReadInbox(self) ==
    /\ inbox[self] > clock[self]
    /\ clock' = [clock EXCEPT ![self] = inbox[self] + 1]
    /\ UNCHANGED << inbox >>

\* Internal increment steps are required if number of processors
\* is 1, otherwise the spec deadlocks.
WorkerInternal(self) ==
    /\ clock' = [clock EXCEPT ![self] = @ + 1]
    /\ UNCHANGED << inbox >>



Worker(self) == 
    \/ WorkerSend(self)
    \/ WorkerReadInbox(self)
    \/ WorkerInternal(self)

Next == \E self \in Proc: Worker(self)

Spec == /\ Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
