# Coins problem

## Problem

See: https://www.glassdoor.com/Interview/software-engineer-interview-questions-SRCH_KO0,17.htm
"""
You have a 100 coins laying flat on a table, each with a head side and a tail side. 10 of them are heads up, 90 are tails up. You can't feel, see or in any other way find out which side is up. Split the coins into two piles such that there are the same number of heads in each pile.
"""

### Run

```bash
pip install hypothesis
pip install pytest
make
```

Output:

```bash
$ make
mypy coins.py --ignore-missing-imports
pytest coins.py --hypothesis-show-statistics
============================================================================================== test session starts ==============================================================================================
platform linux -- Python 3.7.3, pytest-4.3.1, py-1.8.0, pluggy-0.9.0
hypothesis profile 'default' -> database=DirectoryBasedExampleDatabase('/home/toddg/repos/personal/experimental/interview-questions/glassdoor/coins/.hypothesis/examples')
rootdir: /home/toddg/repos/personal/experimental/interview-questions/glassdoor/coins, inifile:
plugins: remotedata-0.3.1, openfiles-0.3.2, doctestplus-0.3.0, arraydiff-0.3, hypothesis-4.23.6
collected 3 items                                                                                                                                                                                               

coins.py ...                                                                                                                                                                                              [100%]
============================================================================================= Hypothesis Statistics =============================================================================================

coins.py::test_generate_random_table:

  - 100 passing examples, 0 failing examples, 0 invalid examples
  - Typical runtimes: 0-4 ms
  - Fraction of time spent in data generation: ~ 28%
  - Stopped because settings.max_examples=100

coins.py::test_generate_divisible_table:

  - 100 passing examples, 0 failing examples, 0 invalid examples
  - Typical runtimes: 0-3 ms
  - Fraction of time spent in data generation: ~ 19%
  - Stopped because settings.max_examples=100

coins.py::test_partition_table:

  - 100 passing examples, 0 failing examples, 0 invalid examples
  - Typical runtimes: 0-5 ms
  - Fraction of time spent in data generation: ~ 19%
  - Stopped because settings.max_examples=100

=========================================================================================== 3 passed in 0.56 seconds ============================================================================================
python3 coins.py
```

### Discussion

This is a lame problem, as it's so poorly defined that it's hard to know if it's a trick or not. However, it's so simple that it can be used to demo `hypothesis` and `pytest`, and `mypy`.


TODO: flesh out the discussion.



## Links
* https://docs.python.org/3/tutorial/datastructures.html
* https://docs.python.org/3/library/typing.html
* https://hypothesis.readthedocs.io/en/latest/details.html
* https://docs.python.org/3.5/library/unittest.html#assert-methods
* https://docs.python.org/3.5/library/unittest.html
* https://docs.python.org/3.5/library/itertools.html#itertools.filterfalse
* https://docs.python.org/3.5/library/functions.html#map
* https://docs.pytest.org/en/latest/example/index.html
* https://docs.pytest.org/en/latest/getting-started.html#our-first-test-run
* https://docs.pytest.org/en/latest/reference.html#pytest-xfail
