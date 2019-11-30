#!/usr/bin/env python3


""" 
Find the root of a given function 'f' where the root is known to be
bracketed between the closed interval of the left and right. The function
iterates until the solution error is below the tolerance.

Args:
    f:          Function to evaluate, takes an 'x'
    left:       LHS bracket
    right:      RHS bracket
    depth:      Current recursion depth
    max_depth:  Maximum recursion depth
    tolerance:  Error must be LEQ to this value for answer to be considered valid

Returns:
    x intercept of function 'f' within provided tolerance.

Raises:
    Exception: Raises an exception if max_depth exceeded.

    >>> bisect(lambda x: x-3, 0, 5, 0, 100, 0.5)
    3.125
    >>> bisect(lambda x: x-3, 0, 5, 0, 100, 0.05)
    3.0078125
    >>> bisect(lambda x: x-3, 0, 5, 0, 100, 0.005)
    3.0029296875
"""
def bisect(f, left, right, depth, max_depth, tolerance):
    if depth > max_depth:
        raise Exception("Max depth [%d] exceeded! left: %d, right: %d, depth: %d" % (max_depth, left, right, depth))
    f_left      = f(left)
    f_right     = f(right)
    middle      = (left + right) / 2.0
    f_middle    = f(middle)
    rel_error   = abs((right - left)/middle)
    #print("left: %f, right: %f, middle: %f, depth: %d, rel_error: %f, tolerance: %f" % (left, right, middle, depth, rel_error, tolerance))
    if rel_error <= tolerance:
        return middle;
    if(f_left * f_middle) <= 0:
        # root is in LH subinterval
        return bisect(f, left, middle, depth + 1, max_depth, tolerance)
    else:
        # root is in RH subinterval
        return bisect(f, middle, right, depth + 1, max_depth, tolerance)


if __name__ == "__main__":
    import doctest
    doctest.testmod()
