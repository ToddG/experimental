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
CONSTANT Procs                  \* processors
ASSUME Cardinality(Procs) > 0   \* we need at least one processor

\* ---------------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------------
VARIABLES 
    inbox,                      \* each clock process has a msg inbox (queue)
    clock,                      \* each clock has it's current value 
    clock_history,              \* each clock has a history of value changes
    pc                          \* program counter

clock_vars  == << inbox, clock, clock_history >>
all_vars    == Append(clock_vars, pc)

\* ---------------------------------------------------------------------------
\* Safety checks (INVARIANTS)
\* ---------------------------------------------------------------------------


\* ---------------------------------------------------------------------------
\* Behaviours
\* ---------------------------------------------------------------------------

\* LABELS = START, STOP, SEND, RCV, INT

Init == 
    /\ inbox = [p \in Procs |-> <<>>]
    /\ clock = [p \in Procs |-> 0]
    /\ clock_history = [p \in Procs |-> <<>>]
    /\ pc = [self \in Procs |-> "START"]

WorkerStart(self) ==
    /\ pc[self] = "START"
      \/ pc' = [pc EXCEPT ![self] = "STOP"]
      \/ pc' = [pc EXCEPT ![self] = "SEND"]
      \/ pc' = [pc EXCEPT ![self] = "RCV"]
      \/ pc' = [pc EXCEPT ![self] = "INT"]
      \/ UNCHANGED clock_vars

WorkerSend(self) ==
    /\ pc[self] = "SEND"
    /\ LET 
            other_clocks == {x \in Procs : x # self}
       IN   /\ clock'[self] = clock[self] + 1
            /\ clock_history'[self = Append(clock_history[self], clock'[self])
            /\ \E target \in other_clocks : 
                    inbox'[target] = Append(inbox[target], clock'[self])
            /\ pc' = [pc EXCEPT ![self] = "START"]
    
WorkerReceive(self) ==
    /\ pc[self] = "RCV"
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED clock_vars

WorkerInternal(self) ==
    /\ pc[self] = "INT"
    /\ clock'[self] = clock[self] + 1
    /\ clock_history'[self] = Append(clock_history[self], clock'[self])
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED inbox

WorkerStop(self) ==
    /\ pc[self] = "STOP"
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED clock_vars

Probe(self) ==
    /\ IF Debug 
        THEN 
            /\ PrintT(("----"))
            /\ PrintT(("Self: " \o ToString(self)))
            /\ PrintT(("Procs: " \o ToString(Procs)))
            /\ PrintT(("clock: " \o ToString(clock)))
            /\ PrintT(("clock_history: " \o ToString(clock_history)))
            /\ PrintT(("inbox: " \o ToString(inbox)))
        ELSE 
            /\ TRUE

Worker(self) == 
    /\ WorkerStart(self)
    /\ WorkerSend(self)
    /\ WorkerReceive(self)
    /\ WorkerInternal(self)
    /\ WorkerStop(self)
    /\ Probe(self)

Next == \E self \in Procs: Worker(self)

Spec == Init /\ [][Next]_clock_vars


(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
*)

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
