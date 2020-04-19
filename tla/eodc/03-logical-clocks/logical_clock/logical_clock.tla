------------------------------ MODULE logical_clock  ------------------------------
EXTENDS TLC
PT == INSTANCE PT
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

CONSTANT Debug                  \* if true then print debug stuff
ASSUME Debug \in {TRUE, FALSE}
CONSTANT Procs          \* processors


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
    ghost_clocks = [p \in Procs |-> <<>>],
    \* initialize the message inbox to empty lists
    inbox   = [p \in Procs |-> <<>>];

\* ---------------------------------------------------------------------------
\* defines (INVARIANTS)
\* ---------------------------------------------------------------------------
\*define
\*    ClocksAlwaysIncrease ==
\*        \A p \in Procs :
\*            if Len(ghost_clocks[p] > 1:
\*                \A m,n : 1..
\*    Invariants == ClocksAlwaysIncrease
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
        print("ghost_clocks: " \o ToString(ghost_clocks));
        print("inbox: " \o ToString(inbox));
    end if;
end macro;

macro increment_clock(increment_proc_id) begin
    with c = clocks[increment_proc_id], g = ghost_clocks[increment_proc_id] do
        \* increment the sender's clock
        c = c + 1;
        clocks[increment_proc_id] := c;
        \* increment the sender's ghost vector clock
        ghost_clocks[increment_proc_id] := Append(g, c)
    end with;
end macro;
\* ---------------------------------------------------------------------------
\* procedures can be called by processes (and can call macros)
\* ---------------------------------------------------------------------------
\* do_send
\*
\*  Send a message to a target process.
\*
\*  Arguments:
\*      ds_sender_proc_id (id)     : process id of the sender
\*      ds_receiver_proc_id (id)   : process id of the receiver
procedure do_send(ds_sender_proc_id, ds_receiver_proc_id)
begin
    PreSend:
    debug("DoSend Before");
    \* simulate sending a message to the receiver by appending to the receiver's
    \* inbox the sender's updated clock value
    DoSend:
    inbox[ds_receiver_proc_id] := Append(inbox[ds_receiver_proc_id], clocks[ds_sender_proc_id]);
    debug("DoSend After");
end procedure;

\* do_receive
\*
\*  Pop messages off the inbox and update clock 
\*
\*  Arguments:
\*      receiver_proc_id (id)   : process id of the receiver
procedure do_receive(r_receiver_proc_id)
    variables
        H = <<>>,
        T = <<>>;
begin
    DoReceive:
    debug("DoReceive Before");
    if inbox[r_receiver_proc_id] # <<>> then
        H := Head(inbox[r_receiver_proc_id]);
        T := Tail(inbox[r_receiver_proc_id]);
        clocks[r_receiver_proc_id] := PT!Max(clocks[r_receiver_proc_id], H) + 1;
        inbox[r_receiver_proc_id] := T;
    end if; 
    debug("DoReceive After");
end procedure;

\* do_internal
\*
\*  Some sort of internal event happened that caused the clock of this
\*  process to increment.
\*
\*  Arguments:
\*      internal_proc_id (id)            : process id
procedure do_internal(i_internal_proc_id)
begin
    DoInternal:
    debug("DoInternal Before");
    clocks[i_internal_proc_id] := clocks[i_internal_proc_id] + 1;
    debug("DoInternal After");
end procedure;

\* ---------------------------------------------------------------------------
\* processes
\* ---------------------------------------------------------------------------
process WorkerProcess \in Procs
    begin
        LogicalClockWorkflow:
        while TRUE do
            either
                ProcSend:
                with p \in Procs \ {self} do
                    call do_send(self, p);
                end with;
            or
                ProcReceive:
                call do_receive(self);
            or
                ProcInternal:
                call do_internal(self);
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
VARIABLES debug, clocks, ghost_clocks, inbox, pc, stack, ds_sender_proc_id, 
          ds_receiver_proc_id, r_receiver_proc_id, H, T, i_internal_proc_id

vars == << debug, clocks, ghost_clocks, inbox, pc, stack, ds_sender_proc_id, 
           ds_receiver_proc_id, r_receiver_proc_id, H, T, i_internal_proc_id
        >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ debug = TRUE
        /\ clocks = [p \in Procs |-> 0]
        /\ ghost_clocks = [p \in Procs |-> <<>>]
        /\ inbox = [p \in Procs |-> <<>>]
        (* Procedure do_send *)
        /\ ds_sender_proc_id = [ self \in ProcSet |-> defaultInitValue]
        /\ ds_receiver_proc_id = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure do_receive *)
        /\ r_receiver_proc_id = [ self \in ProcSet |-> defaultInitValue]
        /\ H = [ self \in ProcSet |-> <<>>]
        /\ T = [ self \in ProcSet |-> <<>>]
        (* Procedure do_internal *)
        /\ i_internal_proc_id = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "LogicalClockWorkflow"]

PreSend(self) == /\ pc[self] = "PreSend"
                 /\ IF debug
                       THEN /\ PrintT(("----"))
                            /\ PrintT(("Name: " \o ToString("DoSend Before")))
                            /\ PrintT(("Self: " \o ToString(self)))
                            /\ PrintT(("Procs: " \o ToString(Procs)))
                            /\ PrintT(("clocks: " \o ToString(clocks)))
                            /\ PrintT(("ghost_clocks: " \o ToString(ghost_clocks)))
                            /\ PrintT(("inbox: " \o ToString(inbox)))
                       ELSE /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "DoSend"]
                 /\ UNCHANGED << debug, clocks, ghost_clocks, inbox, stack, 
                                 ds_sender_proc_id, ds_receiver_proc_id, 
                                 r_receiver_proc_id, H, T, i_internal_proc_id >>

DoSend(self) == /\ pc[self] = "DoSend"
                /\ inbox' = [inbox EXCEPT ![ds_receiver_proc_id[self]] = Append(inbox[ds_receiver_proc_id[self]], clocks[ds_sender_proc_id[self]])]
                /\ IF debug
                      THEN /\ PrintT(("----"))
                           /\ PrintT(("Name: " \o ToString("DoSend After")))
                           /\ PrintT(("Self: " \o ToString(self)))
                           /\ PrintT(("Procs: " \o ToString(Procs)))
                           /\ PrintT(("clocks: " \o ToString(clocks)))
                           /\ PrintT(("ghost_clocks: " \o ToString(ghost_clocks)))
                           /\ PrintT(("inbox: " \o ToString(inbox')))
                      ELSE /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << debug, clocks, ghost_clocks, stack, 
                                ds_sender_proc_id, ds_receiver_proc_id, 
                                r_receiver_proc_id, H, T, i_internal_proc_id >>

do_send(self) == PreSend(self) \/ DoSend(self)

DoReceive(self) == /\ pc[self] = "DoReceive"
                   /\ IF debug
                         THEN /\ PrintT(("----"))
                              /\ PrintT(("Name: " \o ToString("DoReceive Before")))
                              /\ PrintT(("Self: " \o ToString(self)))
                              /\ PrintT(("Procs: " \o ToString(Procs)))
                              /\ PrintT(("clocks: " \o ToString(clocks)))
                              /\ PrintT(("ghost_clocks: " \o ToString(ghost_clocks)))
                              /\ PrintT(("inbox: " \o ToString(inbox)))
                         ELSE /\ TRUE
                   /\ IF inbox[r_receiver_proc_id[self]] # <<>>
                         THEN /\ H' = [H EXCEPT ![self] = Head(inbox[r_receiver_proc_id[self]])]
                              /\ T' = [T EXCEPT ![self] = Tail(inbox[r_receiver_proc_id[self]])]
                              /\ clocks' = [clocks EXCEPT ![r_receiver_proc_id[self]] = PT!Max(clocks[r_receiver_proc_id[self]], H'[self]) + 1]
                              /\ inbox' = [inbox EXCEPT ![r_receiver_proc_id[self]] = T'[self]]
                         ELSE /\ TRUE
                              /\ UNCHANGED << clocks, inbox, H, T >>
                   /\ IF debug
                         THEN /\ PrintT(("----"))
                              /\ PrintT(("Name: " \o ToString("DoReceive After")))
                              /\ PrintT(("Self: " \o ToString(self)))
                              /\ PrintT(("Procs: " \o ToString(Procs)))
                              /\ PrintT(("clocks: " \o ToString(clocks')))
                              /\ PrintT(("ghost_clocks: " \o ToString(ghost_clocks)))
                              /\ PrintT(("inbox: " \o ToString(inbox')))
                         ELSE /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Error"]
                   /\ UNCHANGED << debug, ghost_clocks, stack, 
                                   ds_sender_proc_id, ds_receiver_proc_id, 
                                   r_receiver_proc_id, i_internal_proc_id >>

do_receive(self) == DoReceive(self)

DoInternal(self) == /\ pc[self] = "DoInternal"
                    /\ IF debug
                          THEN /\ PrintT(("----"))
                               /\ PrintT(("Name: " \o ToString("DoInternal Before")))
                               /\ PrintT(("Self: " \o ToString(self)))
                               /\ PrintT(("Procs: " \o ToString(Procs)))
                               /\ PrintT(("clocks: " \o ToString(clocks)))
                               /\ PrintT(("ghost_clocks: " \o ToString(ghost_clocks)))
                               /\ PrintT(("inbox: " \o ToString(inbox)))
                          ELSE /\ TRUE
                    /\ clocks' = [clocks EXCEPT ![i_internal_proc_id[self]] = clocks[i_internal_proc_id[self]] + 1]
                    /\ IF debug
                          THEN /\ PrintT(("----"))
                               /\ PrintT(("Name: " \o ToString("DoInternal After")))
                               /\ PrintT(("Self: " \o ToString(self)))
                               /\ PrintT(("Procs: " \o ToString(Procs)))
                               /\ PrintT(("clocks: " \o ToString(clocks')))
                               /\ PrintT(("ghost_clocks: " \o ToString(ghost_clocks)))
                               /\ PrintT(("inbox: " \o ToString(inbox)))
                          ELSE /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Error"]
                    /\ UNCHANGED << debug, ghost_clocks, inbox, stack, 
                                    ds_sender_proc_id, ds_receiver_proc_id, 
                                    r_receiver_proc_id, H, T, 
                                    i_internal_proc_id >>

do_internal(self) == DoInternal(self)

LogicalClockWorkflow(self) == /\ pc[self] = "LogicalClockWorkflow"
                              /\ \/ /\ pc' = [pc EXCEPT ![self] = "ProcSend"]
                                 \/ /\ pc' = [pc EXCEPT ![self] = "ProcReceive"]
                                 \/ /\ pc' = [pc EXCEPT ![self] = "ProcInternal"]
                              /\ UNCHANGED << debug, clocks, ghost_clocks, 
                                              inbox, stack, ds_sender_proc_id, 
                                              ds_receiver_proc_id, 
                                              r_receiver_proc_id, H, T, 
                                              i_internal_proc_id >>

ProcSend(self) == /\ pc[self] = "ProcSend"
                  /\ \E p \in Procs \ {self}:
                       /\ /\ ds_receiver_proc_id' = [ds_receiver_proc_id EXCEPT ![self] = p]
                          /\ ds_sender_proc_id' = [ds_sender_proc_id EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_send",
                                                                   pc        |->  "LogicalClockWorkflow",
                                                                   ds_sender_proc_id |->  ds_sender_proc_id[self],
                                                                   ds_receiver_proc_id |->  ds_receiver_proc_id[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "PreSend"]
                  /\ UNCHANGED << debug, clocks, ghost_clocks, inbox, 
                                  r_receiver_proc_id, H, T, i_internal_proc_id >>

ProcReceive(self) == /\ pc[self] = "ProcReceive"
                     /\ /\ r_receiver_proc_id' = [r_receiver_proc_id EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_receive",
                                                                 pc        |->  "LogicalClockWorkflow",
                                                                 H         |->  H[self],
                                                                 T         |->  T[self],
                                                                 r_receiver_proc_id |->  r_receiver_proc_id[self] ] >>
                                                             \o stack[self]]
                     /\ H' = [H EXCEPT ![self] = <<>>]
                     /\ T' = [T EXCEPT ![self] = <<>>]
                     /\ pc' = [pc EXCEPT ![self] = "DoReceive"]
                     /\ UNCHANGED << debug, clocks, ghost_clocks, inbox, 
                                     ds_sender_proc_id, ds_receiver_proc_id, 
                                     i_internal_proc_id >>

ProcInternal(self) == /\ pc[self] = "ProcInternal"
                      /\ /\ i_internal_proc_id' = [i_internal_proc_id EXCEPT ![self] = self]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_internal",
                                                                  pc        |->  "LogicalClockWorkflow",
                                                                  i_internal_proc_id |->  i_internal_proc_id[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "DoInternal"]
                      /\ UNCHANGED << debug, clocks, ghost_clocks, inbox, 
                                      ds_sender_proc_id, ds_receiver_proc_id, 
                                      r_receiver_proc_id, H, T >>

WorkerProcess(self) == LogicalClockWorkflow(self) \/ ProcSend(self)
                          \/ ProcReceive(self) \/ ProcInternal(self)

Next == (\E self \in ProcSet:  \/ do_send(self) \/ do_receive(self)
                               \/ do_internal(self))
           \/ (\E self \in Procs: WorkerProcess(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* Liveness checks (PROPERTIES)
    Example of "eventually this is always true..."
        Liveness == <>[](some_value = SomeCheck())
*)

=============================================================================
\* Modification History
\* Created by Todd D. Greenwood-Geer
