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

def generate_divisible_table(num_heads:int, num_tails:int) -> Table:
    if num_heads < 0:
        raise Exception("Invalid input: num_heads >= 0")
    if num_tails < 0:
        raise Exception("Invalid input: num_tails >= 0")
    if num_heads % 2 != 0:
        raise Exception("Invalid input: num_heads must be divisible by 2, found: %d" % num_heads)
    if num_tails % 2 != 0:
        raise Exception("Invalid input: num_tails must be divisible by 2, found: %d" % num_tails)
    return generate_random_table(num_heads, num_tails)

def partition_table(t: Table) -> PTables:
    """
    Partition a random table into two tables, each with equal numbers of HEADS and TAILS
    """
    heads : Table = list(filter(lambda x: x == HEADS, t))
    tails : Table = list(filter(lambda x: x == TAILS, t))
    size_heads = len(heads)
    size_tails = len(tails)
    if size_heads % 2 != 0:
        raise Exception("Invalid input: size_heads in table must be divisible by 2, found: %d" % size_heads)
    if size_tails % 2 != 0:
        raise Exception("Invalid input: size_tails in table must be divisible by 2, found: %d" % size_tails)
    half_heads = int(size_heads/2)
    half_tails = int(size_tails/2)
    note("size_heads/2:%d, size_tails/2:%d, heads:%s, tails:%s" % (half_heads, half_tails, heads, tails))
    ht1 = heads[:half_heads] + tails[:half_tails]
    ht2 = heads[half_heads:] + tails[half_tails:]
    note("ht1:%s, ht2::%s" % (ht1, ht2))
    return (ht1, ht2)


@given(h=st.integers(min_value=-1000, max_value=1000), t=st.integers(min_value=-1000, max_value=1000))
def test_generate_random_table(h,t):
    if h < 0 or t < 0:
        with pytest.raises(Exception, match="Invalid input.*>= 0"):
            rt = generate_random_table(h, t)
    else:
        rt = generate_random_table(h, t)
        sum_tails = len([x for x in rt if x == TAILS])
        sum_heads = len([x for x in rt if x == HEADS])
        note("h:%d, t:%d, table:%s"%(h,t,rt))
        assert h == sum_heads
        assert t == sum_tails

@given(h=st.integers(min_value=0, max_value=1000), t=st.integers(min_value=0, max_value=1000))
def test_generate_divisible_table(h,t):
    if h % 2 != 0 or t % 2 != 0:
        with pytest.raises(Exception, match="Invalid input.* divisible by 2"):
            rt = generate_divisible_table(h, t)
    else:
        rt = generate_divisible_table(h, t)
        sum_tails = len([x for x in rt if x == TAILS])
        sum_heads = len([x for x in rt if x == HEADS])
        note("h:%d, t:%d, table:%s"%(h,t,rt))
        assert h == sum_heads
        assert t == sum_tails

@given(h=st.integers(min_value=0, max_value=1000), t=st.integers(min_value=0, max_value=1000))
def test_partition_table(h,t):
    def verify_partition(p:Table):
        sum_tails = len([x for x in p if x == TAILS])
        sum_heads = len([x for x in p if x == HEADS])
        note("h:%d, t:%d, table:%s, sum_tails:%d, sum_heads:%d"%(h,t,rt, sum_tails, sum_heads))
        if h > 0:
            assert int(h/2) == sum_heads
        else:
            assert sum_heads == 0
        if t > 0:
            assert int(t/2) == sum_tails
        else:
            assert sum_tails == 0

    if h % 2 != 0 or t % 2 != 0:
        with pytest.raises(Exception, match="Invalid input.* divisible by 2"):
            rt = generate_divisible_table(h, t)
    else:
        rt = generate_divisible_table(h, t)
        (pt_left, pt_right) = partition_table(rt)
        verify_partition(pt_left)
        verify_partition(pt_right)


if __name__ == "__main__":
    doctest.testmod()
