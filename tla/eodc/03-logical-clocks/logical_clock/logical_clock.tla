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
            inbox[self] := T;
            clocks_history[self] := Append(clocks_history[self], clocks[self]);
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
                WorkerSend:
                    debug("WorkerSend");
                    clocks[self] := clocks[self] + 1; 
                    clocks_history[self] := Append(clocks_history[self], clocks[self]);
                    with p \in other_procs  do
                        call send_event(p);
                    end with;
            or
                WorkerReceive:
                    debug("WorkerReceive");
                    call receive_event();
            or
                WorkerInternal::
                    debug("WorkerInternal");
                    call increment_clock();
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
\* Label DoIncrement1 of procedure increment_clock at line 53 col 5 changed to DoIncrement1_
\* Label DoIncrement2 of procedure increment_clock at line 65 col 5 changed to DoIncrement2_
\* Label DoIncrement3 of procedure increment_clock at line 53 col 5 changed to DoIncrement3_
CONSTANT defaultInitValue
VARIABLES inbox, clocks, clocks_history, pc, stack

(* define statement *)
ProcValuesNeverExceedMaxValue ==
    \A p \in Procs : ~(clocks[p] > MaxValue)
MaxValueIsAlwaysGreatest ==
    \A p \in Procs : PT!Max(clocks[p], MaxValue) = MaxValue
Invariants ==
    /\ ProcValuesNeverExceedMaxValue
    /\ MaxValueIsAlwaysGreatest

VARIABLES target, other_procs

vars == << inbox, clocks, clocks_history, pc, stack, target, other_procs >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ inbox = [p \in Procs |-> <<>>]
        /\ clocks = [p \in Procs |-> 0]
        /\ clocks_history = [p \in Procs |-> <<>>]
        (* Procedure send_event *)
        /\ target = [ self \in ProcSet |-> defaultInitValue]
        (* Process Worker *)
        /\ other_procs = [self \in Procs |-> {x \in ProcSet : x # self}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LogicalClockWorkflow"]

PreSend(self) == /\ pc[self] = "PreSend"
                 /\ IF Debug
                       THEN /\ PrintT(("----"))
                            /\ PrintT(("Name: " \o ToString(("DoSend Before" \o ToString(target[self])))))
                            /\ PrintT(("Self: " \o ToString(self)))
                            /\ PrintT(("Procs: " \o ToString(Procs)))
                            /\ PrintT(("clocks: " \o ToString(clocks)))
                            /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                            /\ PrintT(("inbox: " \o ToString(inbox)))
                       ELSE /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "DoSend"]
                 /\ UNCHANGED << inbox, clocks, clocks_history, stack, target, 
                                 other_procs >>

DoSend(self) == /\ pc[self] = "DoSend"
                /\ inbox' = [inbox EXCEPT ![target[self]] = Append(inbox[target[self]], clocks[self])]
                /\ IF Debug
                      THEN /\ PrintT(("----"))
                           /\ PrintT(("Name: " \o ToString("DoSend After")))
                           /\ PrintT(("Self: " \o ToString(self)))
                           /\ PrintT(("Procs: " \o ToString(Procs)))
                           /\ PrintT(("clocks: " \o ToString(clocks)))
                           /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                           /\ PrintT(("inbox: " \o ToString(inbox')))
                      ELSE /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ target' = [target EXCEPT ![self] = Head(stack[self]).target]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << clocks, clocks_history, other_procs >>

send_event(self) == PreSend(self) \/ DoSend(self)

DoIncrement1_(self) == /\ pc[self] = "DoIncrement1_"
                       /\ IF Debug
                             THEN /\ PrintT(("----"))
                                  /\ PrintT(("Name: " \o ToString("DoIncrement Before")))
                                  /\ PrintT(("Self: " \o ToString(self)))
                                  /\ PrintT(("Procs: " \o ToString(Procs)))
                                  /\ PrintT(("clocks: " \o ToString(clocks)))
                                  /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                  /\ PrintT(("inbox: " \o ToString(inbox)))
                             ELSE /\ TRUE
                       /\ IF clocks[self] < MaxValue
                             THEN /\ pc' = [pc EXCEPT ![self] = "DoIncrement2_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "DoIncrement3_"]
                       /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                       target, other_procs >>

DoIncrement2_(self) == /\ pc[self] = "DoIncrement2_"
                       /\ IF clocks[self] < MaxValue
                             THEN /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                                  /\ clocks_history' = [clocks_history EXCEPT ![self] = Append(clocks_history[self], clocks'[self])]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << clocks, clocks_history >>
                       /\ pc' = [pc EXCEPT ![self] = "DoIncrement3_"]
                       /\ UNCHANGED << inbox, stack, target, other_procs >>

DoIncrement3_(self) == /\ pc[self] = "DoIncrement3_"
                       /\ IF Debug
                             THEN /\ PrintT(("----"))
                                  /\ PrintT(("Name: " \o ToString("DoIncrement After")))
                                  /\ PrintT(("Self: " \o ToString(self)))
                                  /\ PrintT(("Procs: " \o ToString(Procs)))
                                  /\ PrintT(("clocks: " \o ToString(clocks)))
                                  /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                  /\ PrintT(("inbox: " \o ToString(inbox)))
                             ELSE /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << inbox, clocks, clocks_history, target, 
                                       other_procs >>

increment_clock(self) == DoIncrement1_(self) \/ DoIncrement2_(self)
                         \/ DoIncrement3_(self)

DoIncrement1(self) == /\ pc[self] = "DoIncrement1"
                      /\ IF Debug
                            THEN /\ PrintT(("----"))
                                 /\ PrintT(("Name: " \o ToString("DoIncrement Before")))
                                 /\ PrintT(("Self: " \o ToString(self)))
                                 /\ PrintT(("Procs: " \o ToString(Procs)))
                                 /\ PrintT(("clocks: " \o ToString(clocks)))
                                 /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                 /\ PrintT(("inbox: " \o ToString(inbox)))
                            ELSE /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "DoIncrement2"]
                      /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                      target, other_procs >>

DoIncrement2(self) == /\ pc[self] = "DoIncrement2"
                      /\ IF clocks[self] < MaxValue
                            THEN /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                                 /\ clocks_history' = [clocks_history EXCEPT ![self] = Append(clocks_history[self], clocks'[self])]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << clocks, clocks_history >>
                      /\ pc' = [pc EXCEPT ![self] = "DoIncrement3"]
                      /\ UNCHANGED << inbox, stack, target, other_procs >>

DoIncrement3(self) == /\ pc[self] = "DoIncrement3"
                      /\ IF Debug
                            THEN /\ PrintT(("----"))
                                 /\ PrintT(("Name: " \o ToString("DoIncrement After")))
                                 /\ PrintT(("Self: " \o ToString(self)))
                                 /\ PrintT(("Procs: " \o ToString(Procs)))
                                 /\ PrintT(("clocks: " \o ToString(clocks)))
                                 /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                                 /\ PrintT(("inbox: " \o ToString(inbox)))
                            ELSE /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << inbox, clocks, clocks_history, target, 
                                      other_procs >>

do_internal(self) == DoIncrement1(self) \/ DoIncrement2(self)
                        \/ DoIncrement3(self)

LogicalClockWorkflow(self) == /\ pc[self] = "LogicalClockWorkflow"
                              /\ \/ /\ pc' = [pc EXCEPT ![self] = "ProcSend"]
                                 \/ /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "LogicalClockWorkflow"]
                              /\ UNCHANGED << inbox, clocks, clocks_history, 
                                              stack, target, other_procs >>

ProcSend(self) == /\ pc[self] = "ProcSend"
                  /\ PrintT(("Procs: " \o ToString(Procs)))
                  /\ PrintT(("ProcSet: " \o ToString(ProcSet)))
                  /\ PrintT(("Self: " \o ToString(self)))
                  /\ \E p \in other_procs[self]:
                       /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_event",
                                                                   pc        |->  "LogicalClockWorkflow",
                                                                   target    |->  target[self] ] >>
                                                               \o stack[self]]
                          /\ target' = [target EXCEPT ![self] = p]
                       /\ pc' = [pc EXCEPT ![self] = "PreSend"]
                  /\ UNCHANGED << inbox, clocks, clocks_history, other_procs >>

Worker(self) == LogicalClockWorkflow(self) \/ ProcSend(self)

Next == (\E self \in ProcSet:  \/ send_event(self) \/ increment_clock(self)
                               \/ do_internal(self))
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
