# INCREMENTER

## ISSUE

It seems that changes made by one processor are not seen my the other processor. 

### CASE 1 (single proc)

```incrementer.cfg
SPECIFICATION Spec
CONSTANT Debug      = TRUE
CONSTANT Proc       = {p1}
CONSTANT MaxValue   = 10
INVARIANTS
    Invariants
CONSTRAINTS
    ClockConstraint
```

Running this shows a single thread incrementing the single variable `v` monotonically, as we would expect:

```bash
$ tlc incrementer.tla 
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)

(...)

Computing initial states...
Finished computing initial states: 1 distinct state generated at 2020-04-20 12:29:39.
"Proc[p1] v = 0"
"Proc[p1] v = 1"
"Proc[p1] v = 2"
"Proc[p1] v = 3"
"Proc[p1] v = 4"
"Proc[p1] v = 5"
"Proc[p1] v = 6"
"Proc[p1] v = 7"
"Proc[p1] v = 8"
"Proc[p1] v = 9"
"Proc[p1] v = 10"
Model checking completed. No error has been found.

(...)

```

### CASE 2 (two procs)

```incrementer.cfg
SPECIFICATION Spec
CONSTANT Debug      = TRUE
CONSTANT Proc       = {p1, p2}
CONSTANT MaxValue   = 10
INVARIANTS
    Invariants
CONSTRAINTS
    ClockConstraint
```

Running this shows what _seems_ to be two separate threads incrementing a variable, monotonically, but separately...


```bash
$ tlc incrementer.tla

TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Running breadth-first search Model-Checking with fp 17 and seed -6108814598051602586 with 1 worker on 8 cores with 7134MB heap and 64MB offheap memory [pid: 20023] (Linux 4.15.0-96-generic amd64, Ubuntu 11.0.6 x86_64, MSBDiskFPSet, DiskStateQueue).

(...) 

Finished computing initial states: 1 distinct state generated at 2020-04-20 12:35:00.
"Proc[p1] v = 0"
"Proc[p2] v = 0"
"Proc[p1] v = 1"
"Proc[p2] v = 1"
"Proc[p1] v = 2"
"Proc[p2] v = 2"
"Proc[p1] v = 3"
"Proc[p2] v = 3"
"Proc[p1] v = 4"
"Proc[p2] v = 4"
"Proc[p1] v = 5"
"Proc[p2] v = 5"
"Proc[p1] v = 6"
"Proc[p2] v = 6"
"Proc[p1] v = 7"
"Proc[p2] v = 7"
"Proc[p1] v = 8"
"Proc[p2] v = 8"
"Proc[p1] v = 9"
"Proc[p2] v = 9"
"Proc[p1] v = 10"
"Proc[p2] v = 10"
Model checking completed. No error has been found.

(...)

```

### QUESTIONS

* Q: Is there really just one instance of the `v` variable here?
* Q: Is this output some artifact of how PrintT works? Note: I tried moving the print into the `Increment` action, and the output is the same:

```tla+
Increment(p) ==
    /\ v' = v + 1
    /\ PrintT("Proc[" \o ToString(p) \o "] v = " \o ToString(v) \o " to v' = " \o ToString(v'))
```

* Q: From my reading of SpecifyingSystems (page 16), paraphrase, an action is any formula involving primed and unprimed variables. I guess my confusion is w/respect to this... I thought that every action describeda unique point in time. To put it another way, the conjuncts of all the state changes within a given action happen at the same point in time, and are by definition, 'atomic'. It seems that I am misunderstanding something, because if my logic were true, then I would not see p1 and p2 both incrementing from N to N+1 as shown here.

