# Product Memoization

This is the tale of three different algorithms to solve the same problem.

## Problem

```bash
Given an array of numbers, replace each number with the product of 
all the numbers in the array except the number itself *without* 
using division.
```

## Solutions

* All the solutions below use the same `multiply` function. I broke this out as a separate function so that I could see how many times it was being called.

```erlang
multiply(A,B) when is_number(A) andalso is_number(B) -> A*B.
```

* All the solutions get their inputs from the same function, too:

```erlang
replacements(L) ->
    lists:filter(fun(A) -> length(A) > 0 end, [L -- [X] || X <- L]).
```

The `replacements` function takes a list of items and returns a list of items minus the one item, for each item in the list...e.g.:

```erlang
L = [1,2,3,4].
replacements(L).
[[1,3,4],[1,3,4],[1,2,4],[1,2,3]]
```

### Solution #1 : Foldl

Just use a foldl:

```erlang
mult(L, MultFunc) ->
    [lists:foldl(MultFunc, 1, Z) || Z <- replacements(L)].
```

This seems too easy, but it works. And, in fact, it's the fastest of the alternatives.

How expensive is it?

```text
K : Cost for multiplication (MultFunc)
N : Number of elements

(K*(N-1))*N) ~= K*(N^2) ~= O(N^2)
```

### Solution #2 : Pre-calculate

Imagine an upside-down triangle that we are building one node at a time, from right to left:

```text
1)			    E

2)			D - E

3)			D - E
			  DE
4)		    C - D - E
		      CD  DE
		       CDE
```

With this graph pre-calculated, all the final stage has to do is look up the needed nodes from a cache (dict) like so:

```erlang
multm(L, MultFunc) ->
    M = memom(L, MultFunc),
    [fetch(K, M) || K <- replacements(L)].
```

How expensive is this? Well, we have to build the cache and then iterate one last time over the list, so that should be based off of pythoragas triangle...

https://en.wikipedia.org/wiki/1_%2B_2_%2B_3_%2B_4_%2B_%E2%8B%AF


```text
K : Cost for multiplication (MultFunc)
N : Number of elements

N(N+1)/2 ~= O(N^2)
```

### Solution #3 : Binary Search and Cache

In this example, instead of pre-calculating and looking up from a cache, we instead search for the key, and if not found halve the key and search for the keys. In this way, the cache is constructed and should yield fewer multiplications (it does), and be faster (it isn't).

```erlang
multz(L, MultFunc) ->
    F = fun(X, D) -> 
                {_, D1} = fetchz(X, D, MultFunc),
                D1 end,
    R = replacements(L),
    D1 = lists:foldl(F, dict:new(), R),
    [ V || #node{value=V} <- [dict:fetch(K, D1) || K <- R]].
```

Here we are iterating over the replacement lists and populating the dictionary with the results, and then iterating over the replacement lists a second time to return the cached values. The magic is in the `fetchz` function, which caches values after it multiplies them. Because it's a divide and conquer algorithm, it should be faster, right? Well... 


```text
K : Cost for multiplication (MultFunc)
N : Number of elements
CS : Cost to store in cache
CR : Cost to retrieve from cache

Nlog[base2](N)(K + CS + CR)
```

## Profiling with `cprof`

Let's see if the profiled outputs match up to what we'd expect, for runs where N=100.

### Solution #1 `mult`

```erlang
time=: 0.008 s
cprof mult
{memoize,20106,
         [{{memoize,multiply,2},9900},
```
Here we can see that the `multiply` function was called 9900 times, which is 99 * 100. Comparing that with the expected algorithm performance shows:

```text
(K*(N-1))*N) => K(99)(100) == 9900 times
```

Multiply was called the exact expected number of times.

### Solution #2 `multm`

```erlang
time=: 0.085 s
cprof multm
{memoize,42672,
         [{{memoize,multiply,2},5516},
```

```text
N(N+1)/2 => 100(100+1)/2 = (10000 + 100)/2 = 5050 ~= 5516
```

Multiply was called very close to the expected number of times. However, the run time is 10x slower than than `mult` so we'll have to examine this implmentation further to understand what factors are driving this.

### Solution #3 `multz`

```erlang
time=: 0.010 s
cprof multz
{memoize,3857,
          {{memoize,multiply,2},762},
```

Here we invoked multiply less than 1K times.

```text
Nlog[base2](N) => 100*6.64=664 
```

This is close. Multiply was called 762 times and the model predicted 664 times. Not sure what is causing the discrepancy. However, the real question is what is causing this implementation to be slower than `mult`?


## Profiling with `fprof`

To understand what is going on in more detail, we'll have to look at the fprof stats.


### Solution #1 `mult`

```erlang
%% Analysis results:
%                                               CNT       ACC       OWN        
[{ totals,                                     30329,  115.964,  115.799}].  %%%
%                                               CNT       ACC       OWN        
[{ "<0.8.0>",                                  30329,undefined,  115.799}].   %%
 { {memoize,mult,2},                              1,  115.884,    0.005},     %
 { {memoize,'-mult/2-lc$^0/1-0-',2},            101,  114.096,    0.673},     %
 { {lists,foldl,3},                            10000,  113.423,   58.331},     %
 { {memoize,'-mult/1-fun-0-',2},               9900,   54.830,   30.130},     %
 { {memoize,multiply,2},                       9900,   24.660,   24.571},     %
```

#### Questions
* Why is foldl called 10,000 times and not 9,900 times?
* foldl spent ~47% in {memoize,'-mult/1-fun-0-',2} and ~21% in the actual multiply function
{memoize,multiply,2}...is this just a weird artifact and really we spent 47+21=~68% of the time in the multiply function?

#### Summary

```text
foldl (97%) 
	|-> memoize (47%) 
		|-> multiply (21%)
```

So yeah, we spend 97% of our time in foldl, and 47% of that time is spent actually multiplying stuff.

![mult kcachegrind](https://github.com/ToddG/experimental/blob/master/interview-questions/glassdoor/product/erlang/memoize/docs/mult-kcachegrind.png)


### Solution #2 `multm`

```
%% Analysis results:
%                                               CNT       ACC       OWN        
[{ totals,                                     502404, 2256.319, 2250.620}].  %%%
[{ "<0.8.0>",                                  502404,undefined, 2250.620}].   %%
 { {memoize,multm,1},                             1, 2256.236,    0.014},     %
 { {memoize,multm,2},                             1, 2256.222,    0.012},     %
 { {memoize,memom,2},                             1, 2129.220,    0.018},     %
 { {memoize,memo,2},                            101, 2129.153,    0.933},     %
 { {memoize,add_root,2},                        100, 2127.995,    1.458},     %
 { {memoize,add_child_by_key,3},               5050, 2113.871,   54.237},     %
 { {memoize,add_child,3},                      4950, 2103.974,   82.351},     %
 { {dict,on_bucket,3},                         14950,  849.495,  199.245},     %
 { {dict,update,3},                            9900,  746.221,   75.396},     %
 { {dict,fetch,2},                             15516,  635.038,  157.925},     %
 { {dict,store,3},                             5050,  514.447,   43.860},     %
 { {dict,'-update/3-fun-0-',3},                9900,  390.438,   30.851},     %
 { {dict,update_bkt,3},                        60195,  359.535,  281.656},     %
 { {memoize,child,3},                          4950,  289.191,   52.689},     %
 { {dict,fetch_val,2},                         90293,  265.131,  264.474},     %
 { {dict,get_slot,2},                          31698,  254.713,  158.826},     %
 { {dict,maybe_expand,2},                      5050,  171.777,   15.760},     %
 { {dict,maybe_expand_aux,2},                  5050,  155.938,   36.528},     %
 { {dict,'-store/3-fun-0-',3},                 5050,  154.864,   15.857},     %
 { {erlang,setelement,3},                      67938,  152.908,  152.908},     %
 { {dict,store_bkt_val,3},                     31136,  138.991,  137.898},     %
 { {memoize,'-multm/2-lc$^0/1-0-',2},           101,  124.996,    0.739},     %
 { {memoize,fetch,2},                          1232,  124.257,   13.775},     %
 { {erlang,phash,2},                           39085,  116.396,  116.396},     %
 { {dict,get_bucket,2},                        16748,   93.026,   52.850},     %
 { {dict,rehash,4},                            8381,   80.338,   57.430},     %
 { {dict,is_key,2},                            1232,   46.276,   11.190},     %
 { {dict,get_bucket_s,2},                      17742,   42.177,   42.034},     %
 { {lists,split,2},                             566,   38.247,    3.039},     %
 { {memoize,'-add_child/3-fun-0-',2},          4950,   36.829,   24.861},     %
 { {memoize,'-add_child/3-fun-1-',2},          4950,   35.869,   24.305},     %
 { {lists,split,3},                            9791,   35.208,   33.288},     %
 { {memoize,'-multm/1-fun-0-',2},              5516,   32.176,   17.070},     %
 { {dict,put_bucket_s,3},                      1988,   25.188,   15.629},     %
 { {dict,find_key,2},                          5380,   17.594,   17.557},     %
 { {memoize,multiply,2},                       5516,   15.036,   14.703},     %
```

#### Summary

* Dictionary operations are taking up a *lot* of time
* Because it's a silly algorithm, every time we add a node, we update two other nodes leading to dict:updates taking 37% of the time and dict:store taking 22%.

![multm kcachegrind](https://github.com/ToddG/experimental/blob/master/interview-questions/glassdoor/product/erlang/memoize/docs/multm-kcachegrind.png)

### Solution #3 `multz`

```erlang
%% Analysis results:
%                                               CNT       ACC       OWN        
[{ totals,                                     56872,  229.492,  229.021}].  %%%
%                                               CNT       ACC       OWN        
[{ "<0.8.0>",                                  56872,undefined,  229.021}].   %%
 { {memoize,multz,1},                             1,  229.419,    0.010},     %
 { {memoize,multz,2},                             1,  229.409,    0.027},     %
 { {lists,foldl,3},                             101,  220.677,    0.600},     %
 { {memoize,'-multz/2-fun-0-',3},               100,  220.077,    0.490},     %
 { {memoize,fetchz,3},                         1624,  219.562,   21.149},     %
 { {dict,store,3},                             1088,   92.174,    9.022},     %
 { {dict,on_bucket,3},                         1088,   47.213,   13.847},     %
 { {dict,is_key,2},                            1298,   45.656,   10.534},     %
 { {lists,split,2},                             762,   37.168,    3.599},     %
 { {lists,split,3},                            10611,   33.569,   31.583},     %
 { {dict,maybe_expand,2},                      1088,   27.889,    3.229},     %
 { {dict,'-store/3-fun-0-',3},                 1088,   25.760,    3.326},     %
 { {dict,maybe_expand_aux,2},                  1088,   24.660,    6.887},     %
 { {dict,get_slot,2},                          3022,   22.447,   14.425},     %
 { {dict,store_bkt_val,3},                     5423,   22.422,   22.392},     %
 { {dict,fetch,2},                              636,   20.990,    6.053},     %
 { {dict,find_key,2},                          6578,   18.476,   18.476},     %
 { {dict,rehash,4},                            1268,   11.268,    8.389},     %
 { {erlang,phash,2},                           4133,   10.641,   10.641},     %
 { {erlang,setelement,3},                      4827,   10.615,   10.615},     %
 { {dict,get_bucket,2},                        1934,   10.079,    5.723},     %
 { {dict,fetch_val,2},                         2445,    6.967,    6.944},     %
 { {dict,get_bucket_s,2},                      2091,    4.691,    4.691},     %
 { {memoize,'-multz/2-lc$^1/1-1-',2},           101,    4.208,    0.707},     %
 { {memoize,'-multz/1-fun-0-',2},               762,    4.204,    2.306},     %
 { {memoize,replacements,1},                      2,    4.039,    0.015},     %
 { {dict,put_bucket_s,3},                       314,    3.745,    2.347},     %
 { {memoize,'-replacements/1-lc$^0/1-0-',2},    202,    2.062,    1.458},     %
 { {lists,filter,2},                              2,    1.962,    0.007},     %
 { {lists,'-filter/2-lc$^0/1-0-',2},            202,    1.955,    1.384},     %
 { {memoize,multiply,2},                        762,    1.898,    1.898},     %
 { {erlang,'++',2},                             762,    1.705,    1.705},     %
 { {lists,reverse,2},                           762,    1.684,    1.684},     %
 ```

#### Summary

* Dictionary operations are taking up some of the time, about 40%
* But we only call 'multiply' about 700 times

![multz kcachegrind](https://github.com/ToddG/experimental/blob/master/interview-questions/glassdoor/product/erlang/memoize/docs/multz-kcachegrind.png)


## Runtime Stats
