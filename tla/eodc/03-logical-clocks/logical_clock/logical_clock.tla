------------------------------ MODULE logical_clock  ------------------------------
EXTENDS TLC
PT == INSTANCE PT
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

CONSTANT Debug                  \* if true then print debug stuff
ASSUME Debug \in {TRUE, FALSE}
CONSTANT Procs                  \* set of processors
ASSUME Cardinality(Procs) > 0   \* should have 1 or more processors
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
    end if;
end macro;

macro increment(proc) begin
    if clocks[proc] < MaxValue then
        clocks[proc] := clocks[proc] + 1; 
        clocks_history[proc] := Append(clocks_history[proc], clocks[proc]);
    end if;
end macro;

\* ---------------------------------------------------------------------------
\* procedures can be called by processes (and can call macros)
\* ---------------------------------------------------------------------------
\* \* do_send
\* \*
\* \*  Send a message to a target process.
\* \*
\* \*  Arguments:
\* \*      ds_sender_proc_id (id)     : process id of the sender
\* \*      ds_receiver_proc_id (id)   : process id of the receiver
\* procedure do_send(ds_sender_proc_id, ds_receiver_proc_id)
\* begin
\*     PreSend:
\*     debug("DoSend Before");
\*     \* simulate sending a message to the receiver by appending to the receiver's
\*     \* inbox the sender's updated clock value
\*     DoSend:
\*     inbox[ds_receiver_proc_id] := Append(inbox[ds_receiver_proc_id], clocks[ds_sender_proc_id]);
\*     debug("DoSend After");
\* end procedure;
\* 
\* \* do_receive
\* \*
\* \*  Pop messages off the inbox and update clock 
\* \*
\* \*  Arguments:
\* \*      receiver_proc_id (id)   : process id of the receiver
\* procedure do_receive(r_receiver_proc_id)
\*     variables
\*         H = <<>>,
\*         T = <<>>;
\* begin
\*     DoReceive:
\*     debug("DoReceive Before");
\*     if inbox[r_receiver_proc_id] # <<>> then
\*         H := Head(inbox[r_receiver_proc_id]);
\*         T := Tail(inbox[r_receiver_proc_id]);
\*         clocks[r_receiver_proc_id] := PT!Max(clocks[r_receiver_proc_id], H) + 1;
\*         inbox[r_receiver_proc_id] := T;
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
procedure do_increment(proc)
begin
    DoIncrement1:
    debug("DoIncrement Before");
    if clocks[proc] < MaxValue then
        DoIncrement2:
        increment(proc);
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
\*  Arguments:
\*      internal_proc_id (id)            : process id
procedure do_internal(proc)
begin
    DoIncrement1:
    debug("DoIncrement Before");
    DoIncrement2:
    increment(proc);
    DoIncrement3:
    debug("DoIncrement After");
    return;
end procedure;

\* ---------------------------------------------------------------------------
\* processes
\* ---------------------------------------------------------------------------
process Worker \in Procs
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
                CallDoInternal:
                call do_internal(self);
            or
                CallDoIncrement:
                call do_increment(self);
            end either;
        end while;
end process;
end algorithm;
*)
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* PLUSCAL END
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* BEGIN TRANSLATION
\* Label DoIncrement1 of procedure do_increment at line 54 col 5 changed to DoIncrement1_
\* Label DoIncrement2 of procedure do_increment at line 65 col 5 changed to DoIncrement2_
\* Label DoIncrement3 of procedure do_increment at line 54 col 5 changed to DoIncrement3_
\* Parameter proc of procedure do_increment at line 121 col 24 changed to proc_
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

VARIABLES proc_, proc

vars == << inbox, clocks, clocks_history, pc, stack, proc_, proc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ inbox = [p \in Procs |-> <<>>]
        /\ clocks = [p \in Procs |-> 0]
        /\ clocks_history = [p \in Procs |-> <<>>]
        (* Procedure do_increment *)
        /\ proc_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure do_internal *)
        /\ proc = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LogicalClockWorkflow"]

DoIncrement1_(self) == /\ pc[self] = "DoIncrement1_"
                       /\ IF Debug
                             THEN /\ PrintT(("----"))
                                  /\ PrintT(("Name: " \o ToString("DoIncrement Before")))
                                  /\ PrintT(("Self: " \o ToString(self)))
                                  /\ PrintT(("Procs: " \o ToString(Procs)))
                                  /\ PrintT(("clocks: " \o ToString(clocks)))
                                  /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                             ELSE /\ TRUE
                       /\ IF clocks[proc_[self]] < MaxValue
                             THEN /\ pc' = [pc EXCEPT ![self] = "DoIncrement2_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "DoIncrement3_"]
                       /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                       proc_, proc >>

DoIncrement2_(self) == /\ pc[self] = "DoIncrement2_"
                       /\ IF clocks[proc_[self]] < MaxValue
                             THEN /\ clocks' = [clocks EXCEPT ![proc_[self]] = clocks[proc_[self]] + 1]
                                  /\ clocks_history' = [clocks_history EXCEPT ![proc_[self]] = Append(clocks_history[proc_[self]], clocks'[proc_[self]])]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << clocks, clocks_history >>
                       /\ pc' = [pc EXCEPT ![self] = "DoIncrement3_"]
                       /\ UNCHANGED << inbox, stack, proc_, proc >>

DoIncrement3_(self) == /\ pc[self] = "DoIncrement3_"
                       /\ IF Debug
                             THEN /\ PrintT(("----"))
                                  /\ PrintT(("Name: " \o ToString("DoIncrement After")))
                                  /\ PrintT(("Self: " \o ToString(self)))
                                  /\ PrintT(("Procs: " \o ToString(Procs)))
                                  /\ PrintT(("clocks: " \o ToString(clocks)))
                                  /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                             ELSE /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ proc_' = [proc_ EXCEPT ![self] = Head(stack[self]).proc_]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << inbox, clocks, clocks_history, proc >>

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
                            ELSE /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "DoIncrement2"]
                      /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                      proc_, proc >>

DoIncrement2(self) == /\ pc[self] = "DoIncrement2"
                      /\ IF clocks[proc[self]] < MaxValue
                            THEN /\ clocks' = [clocks EXCEPT ![proc[self]] = clocks[proc[self]] + 1]
                                 /\ clocks_history' = [clocks_history EXCEPT ![proc[self]] = Append(clocks_history[proc[self]], clocks'[proc[self]])]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << clocks, clocks_history >>
                      /\ pc' = [pc EXCEPT ![self] = "DoIncrement3"]
                      /\ UNCHANGED << inbox, stack, proc_, proc >>

DoIncrement3(self) == /\ pc[self] = "DoIncrement3"
                      /\ IF Debug
                            THEN /\ PrintT(("----"))
                                 /\ PrintT(("Name: " \o ToString("DoIncrement After")))
                                 /\ PrintT(("Self: " \o ToString(self)))
                                 /\ PrintT(("Procs: " \o ToString(Procs)))
                                 /\ PrintT(("clocks: " \o ToString(clocks)))
                                 /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                            ELSE /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ proc' = [proc EXCEPT ![self] = Head(stack[self]).proc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << inbox, clocks, clocks_history, proc_ >>

do_internal(self) == DoIncrement1(self) \/ DoIncrement2(self)
                        \/ DoIncrement3(self)

LogicalClockWorkflow(self) == /\ pc[self] = "LogicalClockWorkflow"
                              /\ \/ /\ pc' = [pc EXCEPT ![self] = "CallDoInternal"]
                                 \/ /\ pc' = [pc EXCEPT ![self] = "CallDoIncrement"]
                              /\ UNCHANGED << inbox, clocks, clocks_history, 
                                              stack, proc_, proc >>

CallDoInternal(self) == /\ pc[self] = "CallDoInternal"
                        /\ /\ proc' = [proc EXCEPT ![self] = self]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_internal",
                                                                    pc        |->  "LogicalClockWorkflow",
                                                                    proc      |->  proc[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "DoIncrement1"]
                        /\ UNCHANGED << inbox, clocks, clocks_history, proc_ >>

CallDoIncrement(self) == /\ pc[self] = "CallDoIncrement"
                         /\ /\ proc_' = [proc_ EXCEPT ![self] = self]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_increment",
                                                                     pc        |->  "LogicalClockWorkflow",
                                                                     proc_     |->  proc_[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "DoIncrement1_"]
                         /\ UNCHANGED << inbox, clocks, clocks_history, proc >>

Worker(self) == LogicalClockWorkflow(self) \/ CallDoInternal(self)
                   \/ CallDoIncrement(self)

Next == (\E self \in ProcSet: do_increment(self) \/ do_internal(self))
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
