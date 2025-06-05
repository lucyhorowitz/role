from itertools import chain, combinations, product
from string import ascii_lowercase
from collections import defaultdict, Counter

def powerset(iterable):
    """
    Return the powerset of the input iterable as a list of sets.

    Subsets are ordered first by size, then lexicographically (by input order).
    """
    s = set(iterable)
    return [set(sub) for r in range(len(s)+1) for sub in combinations(s, r)]

def multi_powerset(iterable, bound=1):
    """
    Generate all multisets (with repetitions bounded by `bound`) of elements from the given iterable. 
    Repeated elements in the iterable are treated as distinct (i.e. the input iterable should be a set).

    returns a list of Counters, where each Counter represents a multiset.
    """
    el = set(iterable)
    result = []
    for counts in product(range(bound + 1), repeat=len(el)):
        ms = []
        for e, c in zip(el, counts):
            ms.extend([e] * c)
        result.append(Counter(ms))
    return result
    
class ImplicationSpace:
    """
    Base class representing a universe of multisets over a fixed set of bearers.

    Parameters:
    - num_bearers: how many named bearers to include (from 'a', 'b', ...)
    - bound: how many times each bearer may appear in one side of a candidate implication (default 1, which corresponds to usual sets)

    Variables:
    - bearers: list of bearers
    - sets_of_bearers: list of all bounded multisets of bearers, as Counters
    - candidate_implications: list of tuples (A, B) where A, B are from sets_of_bearers
    """
    def __init__(self, num_bearers, bound=1):
        self.num_bearers = num_bearers
        self.bearers = [name for name in ascii_lowercase[:num_bearers]]
        # Generate all multisets, then sort by length and then alphabetically by bearer names
        multisets = list(multi_powerset(self.bearers, bound))
        def multiset_sort_key(ms):
            # Sort by total count (length), then by tuple of (bearer.name, count) pairs
            return (sum(ms.values()), [(b, ms[b]) for b in sorted(ms, key=lambda x: x)])
        self.sets_of_bearers = sorted(multisets, key=multiset_sort_key)
        self.candidate_implications = [(a, b) for a in self.sets_of_bearers for b in self.sets_of_bearers]

class ImplicationFrame(ImplicationSpace):
    def __init__(self, num_bearers, bound=1, example=None):
        """
        Initialize an implication frame with optional example data.

        If no example is provided, prompts the user for which implications should hold
        between each pair of multisets in the space.
        """
        ImplicationSpace.__init__(self, num_bearers, bound)
        size = len(self.sets_of_bearers)
        self.bound = bound

        if example is not None:
            self.implications = example
            return
        
        self.implications = [[None] * size for _ in range(size)]

        for i, A in enumerate(self.sets_of_bearers):
            for j, B in enumerate(self.sets_of_bearers):
                if self.implications[i][j] is None:
                    while True:
                        a_label = '∅' if not A else '{' + ','.join(a for a in A.elements()) + '}'
                        b_label = '∅' if not B else '{' + ','.join(b for b in B.elements()) + '}'
                        ans = input(f"{a_label} |~ {b_label} ? (0/1): ").strip()
                        if ans in {"0", "1"}:
                            self.implications[i][j] = int(ans)
                            break
                        print("please enter 0 or 1")

    def __getitem__(self, key):
        i, j = key
        return self.implications[i][j]

    def __repr__(self):
        return self.pretty()

    # pretty‑print the implication matrix with subset labels
    def _subset_labels(self):
        """internal helper: human‑friendly labels for each subset"""
        return ['∅' if not s else ','.join(b for b in s) for s in self.sets_of_bearers]

    def pretty(self, padding: int = 2) -> str:
        """
        return a string table of the implication matrix.
        `padding` controls spaces around each cell (default 2).
        """
        labels = self._subset_labels()
        col_w = max(len(l) for l in labels) + padding
        sep = '-' * (col_w + 1) + '+' + '+'.join('-' * (col_w + 2) for _ in labels)

        # header row
        out_lines = [' ' * col_w + ' | ' + ' | '.join(f'{lbl:>{col_w}}' for lbl in labels)]
        out_lines.append(sep)

        # body rows
        for lbl, row in zip(labels, self.implications):
            row_str = f'{lbl:>{col_w}} | ' + ' | '.join(f'{val:>{col_w}}' for val in row)
            out_lines.append(row_str)

        return '\n'.join(out_lines)

    def __str__(self):
        return self.pretty()
    
    def is_good(self, premise, conclusion):
        """
        Check whether a candidate implication is good (1) or not (0).
        
        `premise` and `conclusion` can be either: a list of bearers, a Counter of bearers, or the name of a bearer as a string.
        However, the list or Counter must belong to sets_of_bearers, i.e. no bearer can appear more often than the "bound" of the whole frame. 
        """
        if isinstance(premise, list):
            premise = Counter(premise)
        if isinstance(conclusion, list):
            conclusion = Counter(conclusion)
        if isinstance(premise, str):
            premise = Counter([next(b for b in self.bearers if b == premise)])
        if isinstance(conclusion, str):
            conclusion = Counter([next(b for b in self.bearers if b == conclusion)])
        
        # find index of premise multiset
        try:
            p_index = next(i for i, ms in enumerate(self.sets_of_bearers) if Counter(ms) == premise)
        except StopIteration:
            raise ValueError(f"premise {premise} not in this implication frame")
        # find index of conclusion multiset
        try:
            c_index = next(i for i, ms in enumerate(self.sets_of_bearers) if Counter(ms) == conclusion)
        except StopIteration:
            raise ValueError(f"conclusion {conclusion} not in this implication frame")
        # return entry at [row=conclusion, column=premise]
        return self.implications[c_index][p_index]
    
    def RSR(self, candidates):
        return ""

    def _RSR(self, premise, conclusion):
        if isinstance(premise, list):
            premise = Counter(premise)
        if isinstance(conclusion, list):
            conclusion = Counter(conclusion)
        if isinstance(premise, str):
            premise = Counter([next(b for b in self.bearers if b == premise)])
        if isinstance(conclusion, str):
            conclusion = Counter([next(b for b in self.bearers if b == conclusion)])

        result = []
        for a in self.sets_of_bearers:
            for b in self.sets_of_bearers:
                new_p = premise + a
                new_q = conclusion + b
                # skip if adding exceeds bound
                if any(count > self.bound for count in new_p.values()) or any(count > self.bound for count in new_q.values()):
                    continue
                if self.is_good(new_p, new_q):
                    result.append((a, b))
        return result

def main():
    use_def = input("use Zazzles? (y/N) ").strip().lower()
    if use_def == 'y':
        # example for n=2: explicit 4x4 default matrix
        n = 2
        zazzles = [
            [1, 1, 0, 1],
            [0, 1, 0, 1],
            [0, 0, 1, 1],
            [1, 1, 1, 1]
        ]
        f = ImplicationFrame(n, bound=1, example=zazzles)
    else:
        while True:
            try:
                n = int(input("number of bearers? ").strip())
                if n < 0:
                    print("please enter a nonnegative integer.")
                    continue
                break
            except ValueError:
                print("please enter an integer.")
        while True:
            try:
                bound = int(input("bound? ").strip())
                break
            except ValueError:
                print("please enter an integer.")
        f = ImplicationFrame(n, bound)

    print("\nimplication matrix:\n")
    print(f)

if __name__ == "__main__":
    main()