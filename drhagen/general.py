from functools import reduce
from itertools import count
from operator import mul
from typing import Iterable


class Count(Iterable):
    def __init__(self, start: int = 0, step: int = 1):
        self.start = start
        self.step = step

    def __iter__(self):
        return count(self.start, self.step)

    def __getitem__(self, key):
        if isinstance(key, int):
            return self.start + key
        elif isinstance(key, slice):
            # Bounded, use range
            if key.start is None:
                start = self.start
            else:
                start = self.start + self.step * key.start

            if key.stop is None:
                stop = None
            else:
                stop = self.start + self.step * key.stop

            if key.step is None:
                step = self.step
            else:
                step = self.step * key.step

            if stop is None:
                # Unbounded, use Count
                return Count(start, step)
            else:
                return range(start, stop, step)
        else:
            raise TypeError(f'Count indexes must be int or slice, not {type(key).__name__}')


def prod(iterable):
    return reduce(mul, iterable, 1)


def floored_root(x, n):
    """Integer component of nth root of x.

    Uses binary search to find the integer y such that y ** n <= x < (y + 1) ** n.

    Adapted from https://stackoverflow.com/a/356206/1485877
    """
    high = 1
    while high ** n <= x:
        high *= 2
    low = high // 2
    while low < high:
        mid = (low + high) // 2
        if low < mid and mid ** n < x:
            low = mid
        elif high > mid and mid ** n > x:
            high = mid
        else:
            return mid
    return mid + 1

def assert_multidimensional_consistency(product, pairing, unpairing):
    dims = 4
    for dim in range(1, dims+1):
        iterables = [Count()] * dim
        for i, elements in zip(range(100), product(*iterables)):
            paired = pairing(*elements)
            unpaired = unpairing(dim, i)
            print(f'{i} == {paired}, {elements} == {unpaired}')
            assert i == paired
            assert elements == unpaired