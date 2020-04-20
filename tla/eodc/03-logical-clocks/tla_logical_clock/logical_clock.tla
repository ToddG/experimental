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
CONSTANT Proc                   \* processors
ASSUME Cardinality(Proc) > 0    \* we need at least
CONSTANT Null

\* ---------------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------------
VARIABLES 
    inbox,                      \* each clock process has a msg inbox (queue)
    read,                       \* messages that the process has read from inbox 
    sent,                       \* each clock process has a history of sent changes
    clock,                      \* each clock has it's current value 
    clock_h,                    \* each clock has a history of value changes
    pc,                         \* program counter
    states                      \* program states

clock_vars  == << inbox, read, sent, clock, clock_h, states>>
vars  == << inbox, read, sent, clock, clock_h, states, pc >>

\* ---------------------------------------------------------------------------
\* Safety checks (INVARIANTS)
\* ---------------------------------------------------------------------------


\* ---------------------------------------------------------------------------
\* Behaviours
\* ---------------------------------------------------------------------------

\* LABELS = START, STOP, SEND, RCV, INT

Init == 
    /\ inbox    = [p \in Proc |-> <<>>]
    /\ sent     = [p \in Proc |-> <<>>]
    /\ read     = [p \in Proc |-> <<>>]
    /\ clock    = [p \in Proc |-> 0]
    /\ clock_h = [p \in Proc |-> <<>>]
    /\ states   = {"START", "SEND", "RCV", "INT"} 
    /\ pc       = [self \in Proc |-> "START"]

(*
EmptyOrNaturalSeq(x) ==
    IF x = <<>>
    THEN TRUE
    ELSE \A m \in x: m \in Nat
*)

TypeInvariant ==
    /\ \A p \in Proc :
        /\ clock[p] \in Nat
        /\ pc[p] \in (states \cup {"PROBE"})
        (*
        /\ EmptyOrNaturalSeq(inbox[p])
        /\ EmptyOrNaturalSeq(sent[p])
        /\ EmptyOrNaturalSeq(read[p])
        /\ EmptyOrNaturalSeq(clock_h[p])
        *)

MyReduceSeq(op(_,_), set, acc) ==
    IF set = <<>>
    THEN acc
    ELSE PT!ReduceSeq(op, set, acc)


MaxClockHist(p)     == MyReduceSeq(PT!Max, clock_h[p], 0)
MaxSent(p)          == MyReduceSeq(PT!Max, sent[p], 0)
MaxRead(p)          == MyReduceSeq(PT!Max, read[p], 0)
MaxInbox(p)         == MyReduceSeq(PT!Max, inbox[p], 0)

Coherence ==
    /\ \A p \in Proc :
        /\ clock[p] = MaxClockHist(p)
        /\ clock[p] >= MaxSent(p)

Invariants ==
    /\ TypeInvariant
    /\ Coherence

WorkerStart(self) ==
    /\ pc[self] = "START"
    /\ \E s \in ((states) \ {"START"}) : pc' = [pc EXCEPT ![self] = s]
    /\ UNCHANGED clock_vars

WorkerSend(self) ==
    LET 
        other_clocks == {x \in Proc : x # self}
        next_clock == clock[self] + 1
    IN  
        /\ pc[self] = "SEND"
        /\ clock' = [clock EXCEPT ![self] = next_clock]
        /\ clock_h'= [clock_h EXCEPT ![self] = Append(@, next_clock)]
        /\ \E target \in other_clocks : 
                /\ inbox' = [inbox EXCEPT ![target] = Append(@, next_clock)]
                /\ sent' = [sent EXCEPT ![self] = Append(@, next_clock)]
        /\ pc' = [pc EXCEPT ![self] = "PROBE"]
        /\ UNCHANGED <<read, states>>
    
WorkerReadInbox(self) ==
    /\ pc[self] = "RCV"
    /\ IF inbox[self] # <<>>
        THEN
            LET 
                inbox_max == PT!ReduceSeq(PT!Max, inbox[self], 0)
            IN 
                /\ IF inbox_max > clock[self]
                    THEN
                        /\ clock' = [clock EXCEPT ![self] = inbox_max + 1]
                        /\ clock_h' = [clock_h EXCEPT ![self] = Append(@, inbox_max + 1)]
                        /\ read' = [read EXCEPT ![self] = @ \o inbox[self]]
                        /\ inbox' = [inbox EXCEPT ![self] = <<>>]
                        /\ UNCHANGED << sent, states>>
                    ELSE
                        /\ TRUE
                        /\ read' = [read EXCEPT ![self] = @ \o inbox[self]]
                        /\ inbox' = [inbox EXCEPT ![self] = <<>>]
                        /\ UNCHANGED << sent, clock, clock_h, states>>
        ELSE
            /\ TRUE
            /\ UNCHANGED clock_vars
    /\ pc' = [pc EXCEPT ![self] = "PROBE"]

WorkerInternal(self) ==
    LET 
        next_clock == clock[self] + 1
    IN
        /\ pc[self] = "INT"
        /\ clock' = [clock EXCEPT ![self] = next_clock]
        /\ clock_h' = [clock_h EXCEPT ![self] = Append(@, next_clock)]
        /\ pc' = [pc EXCEPT ![self] = "PROBE"]
        /\ UNCHANGED <<inbox, read, sent, states>>

WorkerStop(self) ==
    /\ pc[self] = "STOP"
    /\ UNCHANGED vars

Probe(self) ==
    /\ pc[self] = "PROBE"
    /\ IF Debug 
        THEN 
            /\ PrintT(("----"))
            /\ PrintT(("Self: " \o ToString(self)))
            /\ PrintT(("Proc: " \o ToString(Proc)))
            /\ PrintT(("clock: " \o ToString(clock)))
            /\ PrintT(("clock_h: " \o ToString(clock_h)))
            /\ PrintT(("inbox: " \o ToString(inbox)))
            /\ PrintT(("read: " \o ToString(read)))
            /\ PrintT(("sent: " \o ToString(sent)))
        ELSE 
            /\ TRUE
    /\ pc' = [pc EXCEPT ![self] = "START"]
    /\ UNCHANGED clock_vars

Worker(self) == 
    \/ WorkerStart(self)
    \/ WorkerSend(self)
    \/ WorkerReadInbox(self)
    \/ WorkerInternal(self)
    \/ WorkerStop(self)
    \/ Probe(self)

Next == \E self \in Proc: Worker(self)

Spec == 
    /\ Init /\ [][Next]_vars
    /\ \A self \in Proc: WF_vars(Worker(self))


(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
ClocksAlwaysIncrease ==
    [] \A self \in Proc:
            clock'[self] >= clock[self]
*)


=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
