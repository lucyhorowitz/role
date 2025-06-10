from itertools import chain, combinations, product

def powerset(iterable):
    """
    Return the powerset of the input iterable as a list of sets.

    Subsets are ordered first by size, then lexicographically (by input order).
    """
    #print(iterable)
    s = list(iterable)
    return [list(sub) for r in range(len(s)+1) for sub in combinations(s, r)]

def powerset_iter(seq):
    for r in range(1, len(seq)+1):
        for combo in combinations(seq, r):
            yield combo

def multi_powerset(bearers, bound=1):
    """
    Generate all multisets (with repetitions bounded by `bound`) of elements from the given iterable. 
    Repeated elements in the iterable are treated as distinct (i.e. the input iterable should be a set).

    returns a list of Counters, where each Counter represents a multiset.
    """
    n = len(bearers)
    return sorted([tuple(counts) for counts in product(range(bound + 1), repeat=n)])

def multi_union(a, b, bound=None):
    """component‑wise addition of two count‑tuples, clipped at `bound`."""
    if bound:
        return tuple(min(x + y, bound) for x, y in zip(a, b))
    else:return tuple(x + y for x, y in zip(a, b))

def sub_multiset(t):
    """
    return all sub-multisets of the given tuple `t`
    """
    ranges = [range(x + 1) for x in t]
    return [tuple(counts) for counts in product(*ranges)]

def multi_intersection(t1,t2):
    """
    return the component-wise minimum of two count-tuples (multiset intersection)
    """
    return tuple(min(x, y) for x, y in zip(t1, t2))
