#!/usr/bin/env python3


def root(f, left, right, max_depth, tolerance):
    """
    Find the root of a given function 'f' where the root is known to be
    bracketed between the closed interval of the left and right. The function
    iterates until the solution error is below the specified tolerance.

    Args:
        f:          Function to evaluate, takes an 'x'
        left:       LHS bracket
        right:      RHS bracket
        max_depth:  Maximum recursion depth
        tolerance:  Error must be LEQ to this value for answer to be considered valid

    Returns:
        x intercept of function 'f' within provided tolerance.

    Raises:
        Exception: Raises an exception if max_depth exceeded.

        >>> root(lambda x: x-3, 0, 5, 100, 0.5)
        3.125
        >>> root(lambda x: x-3, 0, 5, 100, 0.05)
        3.0078125
        >>> root(lambda x: x-3, 0, 5, 100, 0.005)
        3.0029296875
    """
    return _bisect(f, left, right, 0, max_depth, tolerance)


def _bisect(f, left, right, depth, max_depth, tolerance):
    if depth > max_depth:
        raise Exception("Max depth [%d] exceeded! left: %d, right: %d, depth: %d" % (max_depth, left, right, depth))
    f_left = f(left)
    middle = (left + right) / 2.0
    f_middle = f(middle)
    rel_error = abs((right - left) / middle)
    if rel_error <= tolerance:
        return middle
    if (f_left * f_middle) <= 0:
        # root is in LHS sub interval
        return _bisect(f, left, middle, depth + 1, max_depth, tolerance)
    else:
        # root is in RHS sub interval
        return _bisect(f, middle, right, depth + 1, max_depth, tolerance)


if __name__ == "__main__":
    import doctest
    doctest.testmod()
