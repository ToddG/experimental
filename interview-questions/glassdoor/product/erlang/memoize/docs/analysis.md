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


