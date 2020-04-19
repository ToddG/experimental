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
CONSTANT Debug                  \* if true then print debug stuff
ASSUME Debug \in BOOLEAN        \* make sure debug is a boolean
CONSTANT Proc                  \* processors
ASSUME Cardinality(Proc) > 0   \* we need at least one processor

\* ---------------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------------
VARIABLES 
    inbox,                      \* each clock process has a msg inbox (queue)
    clock,                      \* each clock has it's current value 
    clock_history,              \* each clock has a history of value changes
    pc,                         \* program counter
    states                      \* program states

clock_vars  == << inbox, clock, clock_history, states>>
all_vars  == << inbox, clock, clock_history, states, pc >>

\* ---------------------------------------------------------------------------
\* Safety checks (INVARIANTS)
\* ---------------------------------------------------------------------------


\* ---------------------------------------------------------------------------
\* Behaviours
\* ---------------------------------------------------------------------------

\* LABELS = START, STOP, SEND, RCV, INT

Init == 
    /\ inbox = [p \in Proc |-> <<>>]
    /\ clock = [p \in Proc |-> 0]
    /\ clock_history = [p \in Proc |-> <<>>]
    \*/\ states = {"START", "STOP", "SEND", "RCV", "INT"} 
    /\ states = {"START", "SEND"} 
    /\ pc = [self \in Proc |-> "START"]

TypeInvariant ==
    /\ pc \in [Proc -> states]

WorkerStart(self) ==
    /\ pc[self] = "START"
    /\ \E s \in states : pc' = [pc EXCEPT ![self] = s]
    /\ UNCHANGED clock_vars

WorkerSend(self) ==
    LET 
        other_clocks == {x \in Proc : x # self}
    IN  /\ pc[self] = "SEND"
        /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
        /\ clock_history'= [clock_history EXCEPT ![self] = Append(@, clock'[self])]
        /\ \E target \in other_clocks : 
                inbox' = [inbox EXCEPT ![target] = Append(@, clock'[self])]
        /\ pc' = [pc EXCEPT ![self] = "START"]
        /\ UNCHANGED <<states>>
    
WorkerReceive(self) ==
    /\ pc[self] = "RCV"
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED clock_vars

WorkerInternal(self) ==
    /\ pc[self] = "INT"
    /\ clock' = [clock EXCEPT ![self] = @ + 1]
    /\ clock_history' = [clock_history EXCEPT ![self] = Append(@, clock'[self])]
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED <<inbox, states>>

WorkerStop(self) ==
    /\ pc[self] = "STOP"
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED clock_vars

Probe(self) ==
    /\ IF Debug 
        THEN 
            /\ PrintT(("----"))
            /\ PrintT(("Self: " \o ToString(self)))
            /\ PrintT(("Proc: " \o ToString(Proc)))
            /\ PrintT(("clock: " \o ToString(clock)))
            /\ PrintT(("clock_history: " \o ToString(clock_history)))
            /\ PrintT(("inbox: " \o ToString(inbox)))
        ELSE 
            /\ TRUE
    /\ UNCHANGED all_vars

Worker(self) == 
    \/ WorkerStart(self)
    \/ WorkerSend(self)
    \/ WorkerReceive(self)
    \/ WorkerInternal(self)
    \/ WorkerStop(self)
    \/ Probe(self)

Next == \E self \in Proc: Worker(self)

Spec == Init /\ [][Next]_all_vars


(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
*)

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
