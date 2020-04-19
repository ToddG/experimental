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
CONSTANT MaxValue               \* maximum value to increment to
ASSUME MaxValue \in Nat \ {0}   \* maximum value should be in 1..Nat

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
define
    ProcValuesNeverExceedMaxValue ==
        \A p \in Procs : ~(clocks[p] > MaxValue)
    MaxValueIsAlwaysGreatest ==
        \A p \in Procs : PT!Max(clocks[p], MaxValue) = MaxValue
    Invariants ==
        /\ ProcValuesNeverExceedMaxValue
        /\ MaxValueIsAlwaysGreatest
end define;

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

macro increment() begin
    if clocks[self] < MaxValue then
        clocks[self] := clocks[self] + 1; 
        clocks_history[self] := Append(clocks_history[self], clocks[self]);
    end if;
end macro;

\* ---------------------------------------------------------------------------
\* procedures can be called by processes (and can call macros)
\* ---------------------------------------------------------------------------
\* do_send
\*
\*  Send a message to a target process.
\*
\*  Arguments:
\*      target (id)     : process id of the target (receiver)
procedure do_send(target)
begin
    PreSend:
    debug("DoSend Before" \o ToString(target));
    \* simulate sending a message to the target by appending to the target's
    \* inbox the source's updated clock value
    DoSend:
    inbox[target] := Append(inbox[target], clocks[self]);
    debug("DoSend After");
    return;
end procedure;

\* \* do_receive
\* \*
\* \*  Pop messages off the inbox and update clock 
\* \*
\* \*  Arguments:
\* \*      receiver (id)   : process id of the receiver
\* procedure do_receive(r_receiver)
\*     variables
\*         H = <<>>,
\*         T = <<>>;
\* begin
\*     DoReceive:
\*     debug("DoReceive Before");
\*     if inbox[r_receiver] # <<>> then
\*         H := Head(inbox[r_receiver]);
\*         T := Tail(inbox[r_receiver]);
\*         clocks[r_receiver] := PT!Max(clocks[r_receiver], H) + 1;
\*         inbox[r_receiver] := T;
\*     end if; 
\*     debug("DoReceive After");
\* end procedure;

\*  do_increment
\* 
\*  Increment the clock value for this proc id, and add the current value
\*  to the clocks_history for this proc id.
\* 
\*     Arguments:
\*         proc (id) : process id
procedure do_increment()
begin
    DoIncrement1:
    debug("DoIncrement Before");
    if clocks[self] < MaxValue then
        DoIncrement2:
        increment();
    end if;
    DoIncrement3:
    debug("DoIncrement After");
    return;
end procedure;

\* 
\* do_internal
\*
\*  Some sort of internal event happened that caused the clock of this
\*  process to increment.
\*
procedure do_internal()
begin
    DoIncrement1:
    debug("DoIncrement Before");
    DoIncrement2:
    increment();
    DoIncrement3:
    debug("DoIncrement After");
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
\*              either
\*                  ProcSend:
\*                  with p \in Procs \ {self} do
\*                      call do_send(self, p);
\*                  end with;
\*              or
\*                  ProcReceive:
\*                  call do_receive(self);
\*                 ProcReceive:
\*                 call do_receive(self);
\*             or
            either
                ProcSend:
                print("Procs: " \o ToString(Procs));
                print("ProcSet: " \o ToString(ProcSet));
                print("Self: " \o ToString(self));
                with p \in other_procs  do
                    call do_send(p);
                end with;
      (*      or
                CallDoInternal:
                call do_internal();
            or
                CallDoIncrement:
            call do_increment();
            *)
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
\* Label DoIncrement1 of procedure do_increment at line 53 col 5 changed to DoIncrement1_
\* Label DoIncrement2 of procedure do_increment at line 65 col 5 changed to DoIncrement2_
\* Label DoIncrement3 of procedure do_increment at line 53 col 5 changed to DoIncrement3_
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
        (* Procedure do_send *)
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

do_send(self) == PreSend(self) \/ DoSend(self)

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

do_increment(self) == DoIncrement1_(self) \/ DoIncrement2_(self)
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
                       /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_send",
                                                                   pc        |->  "LogicalClockWorkflow",
                                                                   target    |->  target[self] ] >>
                                                               \o stack[self]]
                          /\ target' = [target EXCEPT ![self] = p]
                       /\ pc' = [pc EXCEPT ![self] = "PreSend"]
                  /\ UNCHANGED << inbox, clocks, clocks_history, other_procs >>

Worker(self) == LogicalClockWorkflow(self) \/ ProcSend(self)

Next == (\E self \in ProcSet:  \/ do_send(self) \/ do_increment(self)
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
