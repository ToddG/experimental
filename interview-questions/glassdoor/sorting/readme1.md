# Sorting

## Problem PART 1

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

### Discussion

I don't find the answers to be particularly enlightening, so I'm going to generate some inputs and run some sorting algorithms through their paces:

#### Inputs

* Constant value :      [1,1,1,...]
* Pre-sorted :          [1,2,3,...]
* Reverse sorted:       [N, N-1, N-2, ...]
* Random:               [...]
* Interleaved :         [Constant, Pre-sorted, Reverse-sorted, Random, ...]


#### Algorithms

* Insertion Sort
* Quicksort
* Heap Sort
* Bucket Sort

#### Input Data

* https://github.com/ToddG/experimental/blob/master/interview-questions/glassdoor/sorting/erlang/sortz/docs/perf/perf_run.csv

### Results

Determining which sorting algorithm is 'best' for a given use case actually depends on your requirements. If you need the fastest sorter possible, then that's probably quicksort. But if you need good overall performance for a wide variety of input types, you're probably going to want heapsort.

* https://github.com/ToddG/experimental/blob/master/interview-questions/glassdoor/sorting/erlang/sortz/docs/sorting_algorithms_analysis.ipynb

#### Summary
* 'heapsort' had the most consistent performance
* 'quicksort' had the fastest performance
* 'quicksort' had the worst performance

## Links
* http://queirozf.com/entries/pandas-dataframe-plot-examples-with-matplotlib-pyplot
* http://queirozf.com/entries/pandas-dataframe-plot-examples-with-matplotlib-pyplot
* https://en.wikipedia.org/wiki/Self-balancing_binary_search_tree
* https://pandas.pydata.org/pandas-docs/stable/
* https://pandas.pydata.org/pandas-docs/stable/getting_started/10min.html
* https://pandas.pydata.org/pandas-docs/stable/getting_started/basics.html
* https://pandas.pydata.org/pandas-docs/stable/getting_started/comparison/comparison_with_sql.html
* https://pandas.pydata.org/pandas-docs/stable/getting_started/comparison/index.html
* https://pandas.pydata.org/pandas-docs/stable/getting_started/dsintro.html
* https://pandas.pydata.org/pandas-docs/stable/getting_started/tutorials.html
* https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.DataFrame.html
* https://pandas.pydata.org/pandas-docs/stable/reference/api/pandas.DataFrame.plot.html#pandas.DataFrame.plot
* https://pandas.pydata.org/pandas-docs/stable/reference/index.html
* https://pandas.pydata.org/pandas-docs/stable/user_guide/cookbook.html#cookbook-plotting
* https://pandas.pydata.org/pandas-docs/stable/user_guide/visualization.html
* https://pypi.org/project/pandasql/
* https://pythonspot.com/matplotlib-bar-chart/
* https://pythonspot.com/matplotlib-gallery/
* https://stackoverflow.com/questions/42128467/matplotlib-plot-multiple-columns-of-pandas-data-frame-on-the-bar-chart
* https://wavedatalab.github.io/datawithpython/visualize.html
* https://www.sqlite.org/lang_aggfunc.html
* https://www.sqlite.org/lang.html
* http://www.sqltutorial.org/sql-group-by/
* http://www.sqltutorial.org/sql-order-by/

