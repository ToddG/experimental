#! /usr/bin/env python3
from hypothesis import given
from hypothesis import note
from typing import List
from typing import Set
from typing import Tuple
import doctest
import hypothesis.strategies as st
import random as r
import pytest
Index = Set[int]
Table = List[bool]
PTables = Tuple[Table, Table]


HEADS = True
TAILS = False

def generate_random_table(num_heads:int, num_tails:int) -> Table:
    """
    Generate a random list of heads and tails.


    >>> generate_random_table(0,0)
    []
    >>> generate_random_table(0,1)
    [False]
    >>> generate_random_table(0,2)
    [False, False]
    """
    if num_heads < 0:
        raise Exception("Invalid input: num_heads >= 0")
    if num_tails < 0:
        raise Exception("Invalid input: num_tails >= 0")
    table_size = num_tails + num_heads
    if table_size <= 0:
        return []
    table = [TAILS]*table_size
    heads_up : Index = set()
    while len(heads_up) < num_heads:
        heads_up.add(r.randint(0, table_size-1))
    for i in heads_up:
        table[i] = HEADS
    return table

def partition_table(t: Table) -> PTables:
    """
    Partition a random table into two tables, each with equal numbers of HEADS and TAILS
    """
    t1 : Table = []
    t2 : Table = []
    return (t1, t2)


@given(h=st.integers(min_value=-1000, max_value=1000), t=st.integers(min_value=-1000, max_value=1000))
def test_generate_random_table(h,t):
    rt = None
    if h < 0 or t < 0:
        with pytest.raises(Exception, match="Invalid input"):
            rt = generate_random_table(h, t)
    else:
        rt = generate_random_table(h, t)
        sum_tails = len([x for x in rt if x == TAILS])
        sum_heads = len([x for x in rt if x == HEADS])
        note("h:%d, t:%d, table:%s"%(h,t,rt))
        assert h == sum_heads
        assert t == sum_tails


if __name__ == "__main__":
    doctest.testmod()
