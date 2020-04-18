------------------------------ MODULE logical_clock  ------------------------------
EXTENDS TLC
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

CONSTANT Procs                  \* set of processors
ASSUME Cardinality(Procs) > 0   \* number of processors > 0


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
    \* initialize all the clocks to zero
    clocks  = [p \in Procs |-> 0],
    \* initialize the message inbox to empty lists
    inbox   = [p \in Procs |-> <<>>];

\* ---------------------------------------------------------------------------
\* defines (INVARIANTS)
\* ---------------------------------------------------------------------------
\*define
\*end define;


\* ---------------------------------------------------------------------------
\* macros can be called by procedures and processes
\* ---------------------------------------------------------------------------
macro add_message(receiver_process_id, sender_clock_value) begin
    inbox[receiver_process_id] := inbox[receiver_process_id] \o sender_clock_value;
end macro;

\* ---------------------------------------------------------------------------
\* procedures can be called by processes (and can call macros)
\* ---------------------------------------------------------------------------
\* do_send
\*
\*  Send a message to a target process.
\*
\*  Arguments:
\*      sender_proc_id (id)     : process id of the sender
\*      receiver_proc_id (id)   : process id of the receiver
procedure do_send(sender_proc_id, receiver_proc_id)
begin
    DoSend:
    clocks[sender_proc_id] := clocks[sender_proc_id] + 1;
    add_message(receiver_proc_id, clocks[sender_proc_id]);
end procedure;

\* do_receive
\*
\*  Pop messages off the inbox and update clock 
\*
\*  Arguments:
\*      sender_proc_id (id)     : process id of the sender
\*      receiver_proc_id (id)   : process id of the receiver
procedure do_receive(receiver_proc_id)
    variables
        H = <<>>,
        T = <<>>;
begin
    DoReceive:
    H := Head(inbox[receiver_proc_id]);
    T := Tail(inbox[receiver_proc_id]);
    if H # <<>>
    then
        clocks[receiver_proc_id] := max(clocks[receiver_proc_id], H) + 1;
        inbox[receiver_proc_id] := T;
    end if; 
end procedure;

\* do_internal
\*
\*  Some sort of internal event happened that caused the clock of this
\*  process to increment.
\*
\*  Arguments:
\*      proc_id (id)            : process id
procedure do_internal(proc_id)
begin
    DoInternal:
    clocks[proc_id] := clocks[proc_id] + 1;
end procedure;

\* ---------------------------------------------------------------------------
\* processes
\* ---------------------------------------------------------------------------
process Proc \in Procs
    begin
        LogicalClockWorkflow:
        while TRUE do
            either
                ProcSend:
                call do_send(self, p \in Procs)
            or
                ProcReceive:
                call do_receive(self)
            or
                ProcInternal:
                call do_internal(self)
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
VARIABLES proc_values, pc, stack

(* define statement *)
ProcValuesNeverExceedMaxValue ==
    \A p \in Procs : ~(proc_values[p] > MaxValue)

VARIABLES x, proc, procedure_local_y_not_used, proc_local_var_a

vars == << proc_values, pc, stack, x, proc, procedure_local_y_not_used, 
           proc_local_var_a >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ proc_values = [p \in Procs |-> 0]
        (* Procedure do_increment *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ proc = [ self \in ProcSet |-> defaultInitValue]
        /\ procedure_local_y_not_used = [ self \in ProcSet |-> 0]
        (* Process Proc *)
        /\ proc_local_var_a = [self \in Procs |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ProcLabel1"]

ProcedureLabel1(self) == /\ pc[self] = "ProcedureLabel1"
                         /\ IF x[self] < MaxValue
                               THEN /\ x' = [x EXCEPT ![self] = x[self] + 1]
                                    /\ proc_values' = [proc_values EXCEPT ![proc[self]] = x'[self]]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << proc_values, x >>
                         /\ pc' = [pc EXCEPT ![self] = "ProcedureLabel1"]
                         /\ UNCHANGED << stack, proc, 
                                         procedure_local_y_not_used, 
                                         proc_local_var_a >>

ProcedureLabel2(self) == /\ pc[self] = "ProcedureLabel2"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ procedure_local_y_not_used' = [procedure_local_y_not_used EXCEPT ![self] = Head(stack[self]).procedure_local_y_not_used]
                         /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
                         /\ proc' = [proc EXCEPT ![self] = Head(stack[self]).proc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << proc_values, proc_local_var_a >>

do_increment(self) == ProcedureLabel1(self) \/ ProcedureLabel2(self)

ProcLabel1(self) == /\ pc[self] = "ProcLabel1"
                    /\ /\ proc' = [proc EXCEPT ![self] = self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_increment",
                                                                pc        |->  "ProcLabel1",
                                                                procedure_local_y_not_used |->  procedure_local_y_not_used[self],
                                                                x         |->  x[self],
                                                                proc      |->  proc[self] ] >>
                                                            \o stack[self]]
                       /\ x' = [x EXCEPT ![self] = proc_local_var_a[self]]
                    /\ procedure_local_y_not_used' = [procedure_local_y_not_used EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ProcedureLabel1"]
                    /\ UNCHANGED << proc_values, proc_local_var_a >>

Proc(self) == ProcLabel1(self)

Next == (\E self \in ProcSet: do_increment(self))
           \/ (\E self \in Procs: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
*)

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
