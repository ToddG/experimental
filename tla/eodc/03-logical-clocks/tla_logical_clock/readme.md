# TLA+ Logical Clock Spec

Adventures in using TLA+ to create a spec for a logical clock, as specified in [GARG](https://www.powells.com/searchresults?keyword=garg+elements+of+distibuted+computing)

## Problem

(See page 31-33)

Verify:

```
\A s <\in S : s -> t => s.c < t.c
```

In my first reading of the algorithm in Figure 3.2 and 3.3, I wasn't sure if this was increment s and then send s, or send s and then set t = s + 1. After reading over this a few times it's clear that it's the latter. I'll go through both of these ideas and see how they play out.

## Solutions

### Solution1

Pseudocode for WorkerIncrementAndThenSend:

```
    /\ next_clock == clock[self] + 1
    /\ clock' = [clock EXCEPT ![self] = next_clock]
    /\ inbox' = [inbox EXCEPT ![target] = Append(@, next_clock)]
```

The full code for this action is:

```
WorkerIncrementSAndThenSendToT(self) ==
    /\ Cardinality(Proc) > 1
    /\ LET 
            other_clocks == {x \in Proc : x # self}
            next_clock == clock[self] + 1
        IN  
            /\ clock' = [clock EXCEPT ![self] = next_clock]
            /\ clock_h'= [clock_h EXCEPT ![self] = Append(@, next_clock)]
            /\ \E target \in other_clocks : 
                    /\ inbox' = [inbox EXCEPT ![target] = Append(@, next_clock)]
                    /\ sent' = [sent EXCEPT ![self] = Append(@, next_clock)]
            /\ UNCHANGED <<read>>
```

#### A : 1 process

_Increment S, then send incremented S to T_


Update .cfg to run one process:
```
CONSTANT Proc = { p1 }
CONSTANT MaxValue = 2
```

Run
```
tlc -dump dot solution1a.dot logical_clock && dot -Tpng solution1a.dot -o solution1a.png && geeqie solution1a.png
```

This generates the following states:

![solution1a](./solution1a/solution1a.png)

4 states generated, 3 distinct states found.

#### B : 2 processes

Update .cfg to run two processes:
```
CONSTANT Proc = { p1, p2 }
CONSTANT MaxValue = 2
```

Run
```
tlc -dump dot solution1b.dot logical_clock && dot -Tpng solution1b.dot -o solution1b.png && geeqie solution1b.png
```

This generates the following states:

![solution1b](./solution1b/solution1b.png)

637 states generated, 130 distinct states found.

Clearly this is way too many states. The problem is the auxillary variables in the spec are being used here.

_Q: What's the idiomatic way in TLA+ to separate out the variables that describe a given algorithm, and the auxillary/ghost variables that are used to verify/prove a given algorithm?_


### Solution2

_Send S + 1 to T_

The key part of this algorithm is this:

```
    /\ inbox' = [inbox EXCEPT ![target] = Append(@, clock[self] + 1)]
```

The full action is:

```
WorkerSendSPlusOneToT(self) ==
    /\ Cardinality(Proc) > 1
    /\ LET 
            other_clocks == {x \in Proc : x # self}
        IN  
            /\ \E target \in other_clocks : 
                    /\ inbox' = [inbox EXCEPT ![target] = Append(@, clock[self])]
                    /\ sent' = [sent EXCEPT ![self] = Append(@, clock[self])]
            /\ UNCHANGED <<read>>
```

#### A : 1 process

```
CONSTANT Proc = { p1 }
CONSTANT MaxValue = 2
```

Run

```
tlc -dump dot solution2a.dot logical_clock && dot -Tpng solution2a.dot -o solution2a.png && geeqie solution2a.png
```

This looks identical to the previous case.


#### B : 2 processes


```
CONSTANT Proc = { p1, p2 }
CONSTANT MaxValue = 2
```

Run

```
tlc -dump dot solution2b.dot logical_clock && dot -Tpng solution2b.dot -o solution2b.png && geeqie solution2b.png
```

Had to cancel the run after a few minutes...

```
Finished computing initial states: 1 distinct state generated at 2020-04-21 15:06:30.
Progress(11) at 2020-04-21 15:06:33: 32,473 states generated (32,473 s/min), 12,927 distinct states found (12,927 ds/min), 6,832 states left on queue.
Progress(16) at 2020-04-21 15:07:33: 1,349,853 states generated (1,317,380 s/min), 415,434 distinct states found (402,507 ds/min), 173,382 states left on queue.
```

Q: How do I limit the state space?

I tried removing the `WorkerInternal` step where the process simply increments it's own clock. This leaves either Send or Read steps:

```
Worker(self) == 
    \/ WorkerSendSPlusOneToT(self)
    \/ WorkerReadInbox(self)
    (*\/ WorkerInternal(self)*)
```

This still turns my laptop into a heating pad...


