# Matrix Summation

* https://www.glassdoor.com/Interview/software-engineer-interview-questions-SRCH_KO0,17.htm

## Problem

```text
Suppose you have a matrix of numbers. How can you easily compute the sum of 
any rectangle (i.e. a range [row_start, row_end, col_start, col_end]) of 
those numbers? How would you code this?
```

### Brainstorming

What does this look like?

```text
    0   1   2   3   4   5
0   1   5   3   8   9   1
1   2   2   2   2   2   2
2   5   4   5   4   5   4
3   3   9   7   3   9   7
4   1   1   1   1   1   1
5   2   2   2   2   3   3
```

So what does suming [1,3,0,2] look like?


```text
    0   1   2   3   4   5
0   
1   2   2   2   
2   5   4   5   
3   3   9   7   
4   
5   
```

Ideas:
* This translates to sum(2,2,2,5,4,5,3,9,7).
* We can `lists:foldl(fun(A,B) -> A + B end, L)` provided I have a way to define `L`.
* Ahhh. So Erlang has the array library, which supports `fold` operations... so it's as simple as folding over a row and folding over cols.
* Ahhh. But wait. Dicts also have fold operations, and this looks much easier.

### Prototyping

1. Fire up erl

```erlang
$ erl
Erlang/OTP 21 [erts-10.3.5.1] [source] [64-bit] [smp:8:8] [ds:8:8:10] [async-threads:1] [hipe]

Eshell V10.3.5.1  (abort with ^G)
```

2. Create a dict

```erlang
1> D = dict:new().
{dict,0,16,16,8,80,48,
      {[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]},
      {{[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]}}}
```

3. Dummy up some data

```erlang
> D1 = dict:store({0,0},100,D).
{dict,1,16,16,8,80,48,
      {[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]},
      {{[],[],
        [[{0,0}|100]],
        [],[],[],[],[],[],[],[],[],[],[],[],[]}}}
> D2 = dict:store({0,1},200,D1).
{dict,2,16,16,8,80,48,
      {[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]},
      {{[],[],
        [[{0,0}|100]],
        [],[],[],[],[],[],[],[],
        [[{0,1}|200]],
        [],[],[],[]}}}
> D3 = dict:store({0,3},300,D2).
{dict,3,16,16,8,80,48,
      {[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]},
      {{[],[],
        [[{0,0}|100]],
        [],[],[],[],[],[],[],[],
        [[{0,1}|200]],
        [],
        [[{0,3}|300]],
        [],[]}}}
```

4. Verify we can retrieve the data

```erlang
> dict:fetch({0,0}, D3).
100
```

5. Create a filter to extract the sub-matrix we want

```erlang
> dict:filter(fun({R,C},_) -> R =:= 0 andalso C >= 1 andalso C =< 3 end, D3). 
{dict,2,16,16,8,80,48,
      {[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]},
      {{[],[],[],[],[],[],[],[],[],[],[],
        [[{0,1}|200]],
        [],
        [[{0,3}|300]],
        [],[]}}}
```

6. Fold over the sub-matrix (really a dict) and sum it

```erlang
> dict:fold(fun(_,V,Acc) -> Acc + V end, 0, dict:filter(fun({R,C},_) -> R =:= 0 andalso C >= 1 andalso C =< 3 end, D3)).
500
```

7. Making this a real function would look like this:

```erlang
sum_matrix(RowStart, RowEnd, ColStart, ColEnd, M) ->
    dict:fold(fun(_,V,Acc) -> Acc + V end, 0, dict:filter(fun({R,C},_) ->   R >= RowStart   andalso 
                                                                            R =< RowEnd     andalso
                                                                            C >= ColStart   andalso
                                                                            C =< ColEnd, M)).
```

### Productize

The Erlang `proper` tests turned out to be almost too easy to write.


### Output

```bash
$ make
cd erlang/matrix && rebar3 do escriptize, eunit, proper
===> Verifying dependencies...
===> Compiling matrix
===> Building escript...
===> Verifying dependencies...
===> Compiling matrix
===> Performing EUnit tests...
....

Top 4 slowest tests (0.013 seconds, 33.3% of total time):
  prop_matrix:prop_test/0: module 'prop_matrix'
    0.013 seconds
  matrix:sum_1x1_test/0
    0.000 seconds
  matrix:sum_4x4_test/0
    0.000 seconds
  matrix:sum_2x2_test/0
    0.000 seconds

Finished in 0.039 seconds
4 tests, 0 failures
===> Verifying dependencies...
===> Compiling matrix
===> Calling deprecated rebar_erlc_compiler compiler module. This module has been replaced by rebar_compiler and rebar_compiler_erl, but will remain available.
===> Testing prop_matrix:prop_test()
....................................................................................................
OK: Passed 100 test(s).
===> 
1/1 properties passed
cd erlang/matrix && _build/default/bin/matrix
Args: []

```


## Links
* http://erlang.org/doc/man/dict.html
* http://erlang.org/doc/man/array.html
* https://stackoverflow.com/questions/536753/using-twomulti-dimensional-array-in-erlang
