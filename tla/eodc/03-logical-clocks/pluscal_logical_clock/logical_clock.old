------------------------------ MODULE logical_clock  ------------------------------
EXTENDS TLC
PT == INSTANCE PT
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

CONSTANT Debug                  \* if true then print debug stuff
ASSUME Debug \in {TRUE, FALSE}
CONSTANT Procs                  \* processors

\* TODO: add more constants here and initialize in the `.cfg` file

\* ---------------------------------------------------------------------------
\* Safety checks (INVARIANTS)
\* ---------------------------------------------------------------------------
\* TODO: add safety checks here


\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* PLUSCAL START
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
(*--algorithm logical_clock

\* ---------------------------------------------------------------------------
\* variables
\* ---------------------------------------------------------------------------
variables
    inbox = [p \in Procs |-> <<>>],
    clocks = [p \in Procs |-> 0],
    clocks_history = [p \in Procs |-> <<>>];

\* ---------------------------------------------------------------------------
\* defines (INVARIANTS)
\* ---------------------------------------------------------------------------
\*define
\*end define;

\* ---------------------------------------------------------------------------
\* macros can be called by procedures and processes
\* ---------------------------------------------------------------------------
macro debug(name) begin
    if Debug then
        print("----");
        print("Name: " \o ToString(name));
        print("Self: " \o ToString(self));
        print("Procs: " \o ToString(Procs));
        print("clocks: " \o ToString(clocks));
        print("clocks_history: " \o ToString(clocks_history));
        print("inbox: " \o ToString(inbox));
    end if;
end macro;

\* ---------------------------------------------------------------------------
\* procedures can be called by processes (and can call macros)
\* ---------------------------------------------------------------------------
\* send_event
\*
\*  Send a message to a target process.
\*
\*  Arguments:
\*      target (id)     : process id of the target 
procedure send_event(target) 
begin
    \* simulate sending a message to the target by appending to the target's
    \* inbox the source's updated clock value
    SendEvent:
    inbox[target] := Append(inbox[target], clocks[self]);
    return;
end procedure;

\* receive_event
\*
\*  Pop messages off the inbox and update clock 
\*
procedure receive_event()
variables
    H = <<>>,
    T = <<>>;
begin
    ReceiveEvent:
        if inbox[self] # <<>> then
            H := Head(inbox[self]);
            T := Tail(inbox[self]);
            clocks[self] := (PT!Max(clocks[self], H) + 1);
            clocks_history[self] := Append(clocks_history[self], clocks[self]);
            inbox[self] := T;
        end if;
    EndReceiveEvent:
    return; 
end procedure;

\*  increment_clock
\* 
\*  Increment the clock value for this proc id, and add the current value
\*  to the clocks_history for this proc id.
\* 
\*     Arguments:
\*         proc (id) : process id
procedure increment_clock() 
begin
    IncrementClock:
    clocks[self] := clocks[self] + 1; 
    clocks_history[self] := Append(clocks_history[self], clocks[self]);
    return;
end procedure;


\* ---------------------------------------------------------------------------
\* processes
\* ---------------------------------------------------------------------------
process Worker \in Procs
    variables
        other_procs = {x \in ProcSet : x # self};
    begin
        LogicalClockWorkflow:
        while TRUE do
            either
                debug("WorkerSend_START");
                WorkerSend:
                    with p \in other_procs do
                        clocks[self] := clocks[self] + 1; 
                        clocks_history[self] := Append(clocks_history[self], clocks[self]);
                        call send_event(p);
                end with;
                WorkerSendDone:
                debug("WorkerSend_END");
            or
                debug("WorkerReceive_START");
                WorkerReceive:
                    call receive_event();
                WorkerReceiveDone:
                debug("WorkerReceive_END");
            or
                debug("WorkerInternal_START");
                WorkerInternal:
                    call increment_clock();
                WorkerInternalDone:
                debug("WorkerInternal_END");
            or
                skip;
            end either;
        end while;
end process;
end algorithm;
*)
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* PLUSCAL END
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES inbox, clocks, clocks_history, pc, stack, target, H, T, other_procs

vars == << inbox, clocks, clocks_history, pc, stack, target, H, T, 
           other_procs >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ inbox = [p \in Procs |-> <<>>]
        /\ clocks = [p \in Procs |-> 0]
        /\ clocks_history = [p \in Procs |-> <<>>]
        (* Procedure send_event *)
        /\ target = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure receive_event *)
        /\ H = [ self \in ProcSet |-> <<>>]
        /\ T = [ self \in ProcSet |-> <<>>]
        (* Process Worker *)
        /\ other_procs = [self \in Procs |-> {x \in ProcSet : x # self}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LogicalClockWorkflow"]

SendEvent(self) == /\ pc[self] = "SendEvent"
                   /\ inbox' = [inbox EXCEPT ![target[self]] = Append(inbox[target[self]], clocks[self])]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ target' = [target EXCEPT ![self] = Head(stack[self]).target]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << clocks, clocks_history, H, T, other_procs >>

send_event(self) == SendEvent(self)

ReceiveEvent(self) == /\ pc[self] = "ReceiveEvent"
                      /\ IF inbox[self] # <<>>
                            THEN /\ H' = [H EXCEPT ![self] = Head(inbox[self])]
                                 /\ T' = [T EXCEPT ![self] = Tail(inbox[self])]
                                 /\ clocks' = [clocks EXCEPT ![self] = (PT!Max(clocks[self], H'[self]) + 1)]
                                 /\ clocks_history' = [clocks_history EXCEPT ![self] = Append(clocks_history[self], clocks'[self])]
                                 /\ inbox' = [inbox EXCEPT ![self] = T'[self]]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << inbox, clocks, clocks_history, 
                                                 H, T >>
                      /\ pc' = [pc EXCEPT ![self] = "EndReceiveEvent"]
                      /\ UNCHANGED << stack, target, other_procs >>

EndReceiveEvent(self) == /\ pc[self] = "EndReceiveEvent"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ H' = [H EXCEPT ![self] = Head(stack[self]).H]
                         /\ T' = [T EXCEPT ![self] = Head(stack[self]).T]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << inbox, clocks, clocks_history, target, 
                                         other_procs >>

receive_event(self) == ReceiveEvent(self) \/ EndReceiveEvent(self)

IncrementClock(self) == /\ pc[self] = "IncrementClock"
                        /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                        /\ clocks_history' = [clocks_history EXCEPT ![self] = Append(clocks_history[self], clocks'[self])]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << inbox, target, H, T, other_procs >>

increment_clock(self) == IncrementClock(self)

LogicalClockWorkflow(self) == /\ pc[self] = "LogicalClockWorkflow"
                              /\ \/ /\ IF Debug
                                          THEN /\ PrintT(("----"))
                                               /\ PrintT(("Name: " \o ToString("WorkerSend_START")))
                                               /\ PrintT(("Self: " \o ToString(self)))
                                               /\ PrintT(("Procs: " \o ToString(Procs)))
                                               /\ PrintT(("clocks: " \o ToString(clocks)))
                                               /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                               /\ PrintT(("inbox: " \o ToString(inbox)))
                                          ELSE /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "WorkerSend"]
                                 \/ /\ IF Debug
                                          THEN /\ PrintT(("----"))
                                               /\ PrintT(("Name: " \o ToString("WorkerReceive_START")))
                                               /\ PrintT(("Self: " \o ToString(self)))
                                               /\ PrintT(("Procs: " \o ToString(Procs)))
                                               /\ PrintT(("clocks: " \o ToString(clocks)))
                                               /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                               /\ PrintT(("inbox: " \o ToString(inbox)))
                                          ELSE /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "WorkerReceive"]
                                 \/ /\ IF Debug
                                          THEN /\ PrintT(("----"))
                                               /\ PrintT(("Name: " \o ToString("WorkerInternal_START")))
                                               /\ PrintT(("Self: " \o ToString(self)))
                                               /\ PrintT(("Procs: " \o ToString(Procs)))
                                               /\ PrintT(("clocks: " \o ToString(clocks)))
                                               /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                               /\ PrintT(("inbox: " \o ToString(inbox)))
                                          ELSE /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "WorkerInternal"]
                                 \/ /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "LogicalClockWorkflow"]
                              /\ UNCHANGED << inbox, clocks, clocks_history, 
                                              stack, target, H, T, other_procs >>

WorkerSend(self) == /\ pc[self] = "WorkerSend"
                    /\ \E p \in other_procs[self]:
                         /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                         /\ clocks_history' = [clocks_history EXCEPT ![self] = Append(clocks_history[self], clocks'[self])]
                         /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_event",
                                                                     pc        |->  "WorkerSendDone",
                                                                     target    |->  target[self] ] >>
                                                                 \o stack[self]]
                            /\ target' = [target EXCEPT ![self] = p]
                         /\ pc' = [pc EXCEPT ![self] = "SendEvent"]
                    /\ UNCHANGED << inbox, H, T, other_procs >>

WorkerSendDone(self) == /\ pc[self] = "WorkerSendDone"
                        /\ IF Debug
                              THEN /\ PrintT(("----"))
                                   /\ PrintT(("Name: " \o ToString("WorkerSend_END")))
                                   /\ PrintT(("Self: " \o ToString(self)))
                                   /\ PrintT(("Procs: " \o ToString(Procs)))
                                   /\ PrintT(("clocks: " \o ToString(clocks)))
                                   /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                   /\ PrintT(("inbox: " \o ToString(inbox)))
                              ELSE /\ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "LogicalClockWorkflow"]
                        /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                        target, H, T, other_procs >>

WorkerReceive(self) == /\ pc[self] = "WorkerReceive"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "receive_event",
                                                                pc        |->  "WorkerReceiveDone",
                                                                H         |->  H[self],
                                                                T         |->  T[self] ] >>
                                                            \o stack[self]]
                       /\ H' = [H EXCEPT ![self] = <<>>]
                       /\ T' = [T EXCEPT ![self] = <<>>]
                       /\ pc' = [pc EXCEPT ![self] = "ReceiveEvent"]
                       /\ UNCHANGED << inbox, clocks, clocks_history, target, 
                                       other_procs >>

WorkerReceiveDone(self) == /\ pc[self] = "WorkerReceiveDone"
                           /\ IF Debug
                                 THEN /\ PrintT(("----"))
                                      /\ PrintT(("Name: " \o ToString("WorkerReceive_END")))
                                      /\ PrintT(("Self: " \o ToString(self)))
                                      /\ PrintT(("Procs: " \o ToString(Procs)))
                                      /\ PrintT(("clocks: " \o ToString(clocks)))
                                      /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                      /\ PrintT(("inbox: " \o ToString(inbox)))
                                 ELSE /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "LogicalClockWorkflow"]
                           /\ UNCHANGED << inbox, clocks, clocks_history, 
                                           stack, target, H, T, other_procs >>

WorkerInternal(self) == /\ pc[self] = "WorkerInternal"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "increment_clock",
                                                                 pc        |->  "WorkerInternalDone" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "IncrementClock"]
                        /\ UNCHANGED << inbox, clocks, clocks_history, target, 
                                        H, T, other_procs >>

WorkerInternalDone(self) == /\ pc[self] = "WorkerInternalDone"
                            /\ IF Debug
                                  THEN /\ PrintT(("----"))
                                       /\ PrintT(("Name: " \o ToString("WorkerInternal_END")))
                                       /\ PrintT(("Self: " \o ToString(self)))
                                       /\ PrintT(("Procs: " \o ToString(Procs)))
                                       /\ PrintT(("clocks: " \o ToString(clocks)))
                                       /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                       /\ PrintT(("inbox: " \o ToString(inbox)))
                                  ELSE /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "LogicalClockWorkflow"]
                            /\ UNCHANGED << inbox, clocks, clocks_history, 
                                            stack, target, H, T, other_procs >>

Worker(self) == LogicalClockWorkflow(self) \/ WorkerSend(self)
                   \/ WorkerSendDone(self) \/ WorkerReceive(self)
                   \/ WorkerReceiveDone(self) \/ WorkerInternal(self)
                   \/ WorkerInternalDone(self)

Next == (\E self \in ProcSet:  \/ send_event(self) \/ receive_event(self)
                               \/ increment_clock(self))
           \/ (\E self \in Procs: Worker(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
*)

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
