# Problem

```bash
Given an array of numbers, replace each number with the product of 
all the numbers in the array except the number itself *without* 
using division.
```

## Initial Thoughts

Brute force, multiply all the items but the current one:
```text
[1]             -> [1]
[1,2]           -> [2,2]
[1,2,3]         -> [2*3, 1*3, 1*2] = [6, 3, 2]
```

Using division, which is forbidden:
```text
1 * 2 * 3 
[6/1    6/2     6/3] -> [6, 3, 2]
```

Is there a way to pre-calculate and use addition?
```text


    1   2   3
1   1   2   3   
2   2   4   6
3   3   6   9


[a, b, c] -> [ b*c, a*c, a*c]
```
I'm sure it's possible to pre-calc an array, but I don't see the pattern yet.

What functional goodies do we have in Erlang?

```erlang
Eshell V10.3.5.1  (abort with ^G)
1> L = [1,2,3,4].
[1,2,3,4]
2> [ L --[X] || X <- L].
[[2,3,4],[1,3,4],[1,2,4],[1,2,3]]
3> [lists:foldl(fun(A,B) -> A*B end,1, Z) || Z <- [L --[X] || X <- L] ].
[24,12,8,6]
```

Ok, easy peasy.

How about in python?

```python
$ ipython
Python 3.7.3 (default, Mar 27 2019, 22:11:17) 
Type 'copyright', 'credits' or 'license' for more information
IPython 7.4.0 -- An enhanced Interactive Python. Type '?' for help.

In [1]: l=[1,2,3,4] 
   ...:                                                                                                                                                                                                          

In [2]: l                                                                                                                                                                                                        
Out[2]: [1, 2, 3, 4]

In [3]: [x for x in l] 
   ...:                                                                                                                                                                                                          
Out[3]: [1, 2, 3, 4]

In [4]: for i,v in enumerate(l): 
   ...:     q = l[:i] + l[i+1:] 
   ...:     print(q) 
   ...:                                                                                                                                                                                                          
[2, 3, 4]
[1, 3, 4]
[1, 2, 4]
[1, 2, 3]

In [5]: [l[:i] + l[i+1:] for i,v in enumerate(l)] 
   ...:                                                                                                                                                                                                          
Out[5]: [[2, 3, 4], [1, 3, 4], [1, 2, 4], [1, 2, 3]]

In [6]: import functools 
   ...: import operator 
   ...: [functools.reduce(operator.mul, x, 1) for x in [l[:i] + l[i+1:] for i,v in enumerate(l)]] 
   ...:                                                                                                                                                                                                          
Out[6]: [24, 12, 8, 6]
```

### Implementation

Let's memoize the computations. If these were expensive to calculate, this would outweigh the costs of storing and retrieving them from a cache.

Q: What is the cost of this memoization?
Q: At what point does it become cost effective to implement?

## Summary

So basically it's the same approach, only Erlang has a much nicer way to extract an element from the list.

* TODO: it'd be cool to memoize this for really large sets of numbers.

## Links
* https://www.glassdoor.com/Interview/software-engineer-interview-questions-SRCH_KO0,17.htm
* https://duckduckgo.com/?q=erlang+foldl&t=canonical&ia=web&iax=qa
* https://stackoverflow.com/questions/3491065/erlang-split-a-list-into-lists-based-on-value
* http://erlang.org/doc/man/lists.html
* https://www.burgaud.com/foldl-foldr-python
* https://www.geeksforgeeks.org/iterate-over-a-list-in-python/
* https://stackoverflow.com/questions/8489250/generate-custom-permutations-with-erlang
* https://stackoverflow.com/questions/34179283/permutations-example-in-erlang
