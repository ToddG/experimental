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


\* ---------------------------------------------------------------------------
\* procedures can be called by processes (and can call macros)
\* ---------------------------------------------------------------------------
\*  do_increment
\* 
\*     Increment the process local variable 'x' _and_ increment the global value
\*     for this proc stored in 'clocks[proc_id]'.
\* 
\*     Arguments:
\*         x (int) : process local variable
\*         proc (id) : process id
procedure do_increment(proc)
    \* procedures can have local vars, this var is not used
    variables
        x;
    begin
        DoIncrement1:
        debug("DoIncrement Before");
        x := clocks[proc];
        if x < MaxValue then
            DoIncrement2:
            x := x + 1;
            clocks[proc] := x;
            clocks_history[proc] := Append(clocks_history[proc], x);
        end if;
        DoIncrement3:
        debug("DoIncrement After");
        DoIncrement4:
        return;
end procedure;



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
\* 
\* \* do_internal
\* \*
\* \*  Some sort of internal event happened that caused the clock of this
\* \*  process to increment.
\* \*
\* \*  Arguments:
\* \*      internal_proc_id (id)            : process id
\* procedure do_internal(i_internal_proc_id)
\* begin
\*     DoInternal1:
\*     debug("DoInternal Before");
\*     DoInternal2:
\*     call do_increment(i_internal_proc_id);
\*     DoInternal3:
\*     debug("DoInternal After");
\* end procedure;

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
        CallDoIncremeent:
        call do_increment(self);
        end while;
end process;
end algorithm;
*)
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* PLUSCAL END
\* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\* BEGIN TRANSLATION
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

VARIABLES proc, x

vars == << inbox, clocks, clocks_history, pc, stack, proc, x >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ inbox = [p \in Procs |-> <<>>]
        /\ clocks = [p \in Procs |-> 0]
        /\ clocks_history = [p \in Procs |-> <<>>]
        (* Procedure do_increment *)
        /\ proc = [ self \in ProcSet |-> defaultInitValue]
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LogicalClockWorkflow"]

DoIncrement1(self) == /\ pc[self] = "DoIncrement1"
                      /\ IF Debug
                            THEN /\ PrintT(("----"))
                                 /\ PrintT(("Name: " \o ToString("DoIncrement Before")))
                                 /\ PrintT(("Self: " \o ToString(self)))
                                 /\ PrintT(("Procs: " \o ToString(Procs)))
                                 /\ PrintT(("clocks: " \o ToString(clocks)))
                                 /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                            ELSE /\ TRUE
                      /\ x' = [x EXCEPT ![self] = clocks[proc[self]]]
                      /\ IF x'[self] < MaxValue
                            THEN /\ pc' = [pc EXCEPT ![self] = "DoIncrement2"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "DoIncrement3"]
                      /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                      proc >>

DoIncrement2(self) == /\ pc[self] = "DoIncrement2"
                      /\ x' = [x EXCEPT ![self] = x[self] + 1]
                      /\ clocks' = [clocks EXCEPT ![proc[self]] = x'[self]]
                      /\ clocks_history' = [clocks_history EXCEPT ![proc[self]] = Append(clocks_history[proc[self]], x'[self])]
                      /\ pc' = [pc EXCEPT ![self] = "DoIncrement3"]
                      /\ UNCHANGED << inbox, stack, proc >>

DoIncrement3(self) == /\ pc[self] = "DoIncrement3"
                      /\ IF Debug
                            THEN /\ PrintT(("----"))
                                 /\ PrintT(("Name: " \o ToString("DoIncrement After")))
                                 /\ PrintT(("Self: " \o ToString(self)))
                                 /\ PrintT(("Procs: " \o ToString(Procs)))
                                 /\ PrintT(("clocks: " \o ToString(clocks)))
                                 /\ PrintT(("clocks_history: " \o ToString(clocks_history)))
                            ELSE /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "DoIncrement4"]
                      /\ UNCHANGED << inbox, clocks, clocks_history, stack, 
                                      proc, x >>

DoIncrement4(self) == /\ pc[self] = "DoIncrement4"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
                      /\ proc' = [proc EXCEPT ![self] = Head(stack[self]).proc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << inbox, clocks, clocks_history >>

do_increment(self) == DoIncrement1(self) \/ DoIncrement2(self)
                         \/ DoIncrement3(self) \/ DoIncrement4(self)

LogicalClockWorkflow(self) == /\ pc[self] = "LogicalClockWorkflow"
                              /\ pc' = [pc EXCEPT ![self] = "CallDoIncremeent"]
                              /\ UNCHANGED << inbox, clocks, clocks_history, 
                                              stack, proc, x >>

CallDoIncremeent(self) == /\ pc[self] = "CallDoIncremeent"
                          /\ /\ proc' = [proc EXCEPT ![self] = self]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_increment",
                                                                      pc        |->  "LogicalClockWorkflow",
                                                                      x         |->  x[self],
                                                                      proc      |->  proc[self] ] >>
                                                                  \o stack[self]]
                          /\ x' = [x EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "DoIncrement1"]
                          /\ UNCHANGED << inbox, clocks, clocks_history >>

Worker(self) == LogicalClockWorkflow(self) \/ CallDoIncremeent(self)

Next == (\E self \in ProcSet: do_increment(self))
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
