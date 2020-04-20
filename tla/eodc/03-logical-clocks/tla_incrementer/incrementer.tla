------------------------------ MODULE incrementer  ------------------------------
EXTENDS TLC
PT == INSTANCE PT
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

CONSTANT Debug                  \* if true then print debug stuff
CONSTANT Proc                   \* set of processors
CONSTANT MaxValue               \* maximum value to increment to

ASSUME DType        == Debug \in {TRUE, FALSE}
ASSUME MVType       == MaxValue \in Nat
ASSUME ProcType     == Cardinality(Proc) > 0

VARIABLES 
    v                           \* the single global variable that is 
                                \* being incremented

vars == << v >>

TypeOK == v \in Nat

Invariants == TypeOK

Init == v = 0

Probe(p) ==
    IF Debug 
    THEN PrintT("Proc[" \o ToString(p) \o "] v = " \o ToString(v))
    ELSE TRUE

Increment(p) ==
    /\ v' = v + 1
    /\ Probe(p)

ClockConstraint ==
    v <= MaxValue

Next == \E p \in Proc : Increment(p)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created by Todd
