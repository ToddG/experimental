# Sorting

## Problem

```text
Q: What sort would you use if you required tight max time bounds and wanted highly regular performance.
```

There were some answers...

```text
6 Answers

    Vector sort.

    Guaranteed to be O(n log n) performance. No better, no worse.

    That is so say, a "Balanced Tree Sort" is guaranteed to be O(n log n) always.
```

## Discussion

I don't find the answers to be particularly enlightening, so I'm going to generate some inputs and run some sorting algorithms through their paces:

### Inputs

* Constant value :      [1,1,1,...]
* Pre-sorted :          [1,2,3,...]
* Reverse sorted:       [N, N-1, N-2, ...]
* Random:               [...]
* Interleaved :         [Constant, Pre-sorted, Reverse-sorted, Random, ...]


### Algorithms

* Insertion Sort
* Quicksort
* Selection Sort
* Heap Sort
* Counting Sort
* Bucket Sort
* Self Balancing Binary Search Tree


## Framework

* Basic tests to verify algorithm correctness : [eunit, proper]
* Perf tests that will run against each algorithm, in series
* Measure:
    * total wall clock time
    * counts of the inner comparator function


## Links

* https://en.wikipedia.org/wiki/Self-balancing_binary_search_tree
