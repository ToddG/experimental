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
    clocks,                     \* each clock has it's current value 
    clocks_history,             \* each clock has a history of value changes
    pc                          \* program counter

vars == << inbox, clocks, clocks_history, pc >>

\* ---------------------------------------------------------------------------
\* Safety checks (INVARIANTS)
\* ---------------------------------------------------------------------------


\* ---------------------------------------------------------------------------
\* Behaviours
\* ---------------------------------------------------------------------------

\* LABELS = START, STOP, SEND, RCV, INT

ProcSet == (Procs)

Init == (* Global variables *)
    /\ inbox = [p \in Procs |-> <<>>]
    /\ clocks = [p \in Procs |-> 0]
    /\ clocks_history = [p \in Procs |-> <<>>]
    /\ pc = [self \in ProcSet |-> "START"]


WorkerStart(self) ==
    /\ pc[self] = "START"
    /\ UNCHANGED vars

WorkerSend(self) ==
    /\ pc[self] = "SEND"
    /\ UNCHANGED vars
    
WorkerReceive(self) ==
    /\ pc[self] = "RCV"
    /\ UNCHANGED vars

WorkerInternal(self) ==
    /\ pc[self] = "INT"
    /\ UNCHANGED vars

WorkerStop(self) ==
    /\ pc[self] = "STOP"
    /\ UNCHANGED vars

Worker(self) == 
    /\ WorkerStart(self)
    /\ WorkerSend(self)
    /\ WorkerReceive(self)
    /\ WorkerInternal(self)
    /\ WorkerStop(self)

Next == \E self \in Procs: Worker(self)

Spec == Init /\ [][Next]_vars


(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
*)

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
