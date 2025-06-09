from itertools import chain, combinations, product
from string import ascii_lowercase
from collections import defaultdict, Counter
import time
from pysat.examples.hitman import Hitman
from pysat.solvers import Solver

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

def add_counts(a, b, bound):
    """component‑wise addition of two count‑tuples, clipped at `bound`."""
    return tuple(min(x + y, bound) for x, y in zip(a, b))

def subcounters(t):
    """
    return all sub-multisets of the given tuple `t`
    """
    ranges = [range(x + 1) for x in t]
    return [tuple(counts) for counts in product(*ranges)]
    
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
        BEARERS = tuple("abcdefghijklmnopqrstuvwxyz"[:num_bearers]) 
        self.bearers = [name for name in BEARERS]
        # generate all multisets, then order by size and, within each size,
        # alphabetically by the *string* of bearer names (e.g. '', 'a', 'b', 'aa', 'ab', 'bb', ...)
        multisets = list(multi_powerset(self.bearers, bound))
        def multiset_sort_key(ms):
            size = sum(ms)
            label = ''.join(b * c for b, c in zip(self.bearers, ms))
            return (size, label)
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
        else:
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

        # pre‑compute the RSR and role for every candidate implication
        self.RSRs, self.roles = {}, {}
        for (p, q) in self.candidate_implications:
            self.RSRs[(p, q)] = frozenset(self._RSR(p, q))
        self.atomic_roles = frozenset(self.RSRs)
        #for (p, q) in self.candidate_implications:
        #    self.roles[(p, q)] = self.role([(p, q)])
                            
    
    def __getitem__(self, key):
        i, j = key
        return self.implications[i][j]

    def __repr__(self):
        return self.pretty()

    # pretty‑print the implication matrix with subset labels (including multiplicities)
    def _subset_labels(self):
        """internal helper: human‑friendly labels for each subset (including multiplicities)"""
        labels = []
        for counts in self.sets_of_bearers:
            if sum(counts) == 0:
                labels.append('∅')
            else:
                # s is a Counter: use elements() to repeat each element by its count
                elems = []
                for b, c in zip(self.bearers, counts):
                    elems.extend([b] * c)
                labels.append(','.join(elems))
        return labels

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
    
    def _to_tuple(self, x):
        counts = [0] * self.num_bearers
        if not x:
            return tuple(counts)
        if isinstance(x, tuple):
            return x
        if isinstance(x, list):
            for b in x:
                counts[self.bearers.index(b)] += 1
            return tuple(counts)
        if isinstance(x, str):
            counts[self.bearers.index(x)] = 1
            return tuple(counts)
        raise TypeError("premise/conclusion must be tuple, list, str or empty")
    
    def _fix_pq(self, premise, conclusion):      
        return self._to_tuple(premise), self._to_tuple(conclusion)

    def is_good(self, premise, conclusion):
        """
        Check whether a candidate implication is good (1) or not (0).
        
        `premise` and `conclusion` can be either: a list of bearers, a tuple of counts, or the name of a bearer as a string.
        However, the list or tuple must belong to sets_of_bearers, i.e. no bearer can appear more often than the "bound" of the whole frame. 
        """
        premise, conclusion = self._fix_pq(premise,conclusion)
        
        # find index of premise multiset
        try:
            p_index = self.sets_of_bearers.index(premise)
        except ValueError:
            raise ValueError(f"premise {premise} not in this implication frame")
        # find index of conclusion multiset
        try:
            c_index = self.sets_of_bearers.index(conclusion)
        except ValueError:
            raise ValueError(f"conclusion {conclusion} not in this implication frame")
        return self.implications[p_index][c_index]
    
    def RSR(self, candidates):
        """
        intersection of the RSRs for each (premise, conclusion) in `candidates`.

        `candidates` is an iterable of pairs. the pairs may contain lists,
        tuples, strings, or the empty string/tuple; they are normalised via
        `_fix_pq` exactly once here.

        results are cached in `self.RSRs` using the normalised tuple of pairs
        as the key.
        """
        #norm = tuple(self._fix_pq(p, q) for (p, q) in candidates)
        #if candidates in self.RSRs:
        #    return self.RSRs[candidates]
        if not candidates:
            return[]
        
        base = self._RSR(*candidates[0])
        for prem, concl in candidates[1:]:
            nxt = self._RSR(prem, concl)
            base = [pair for pair in base if pair in nxt]
            if not base:
                break
        self.RSRs[candidates] = base
        return base

    def _RSR(self, premise, conclusion):
        if (premise,conclusion) in self.RSRs:
            return self.RSRs[(premise,conclusion)]
        result = []
        for (p,q) in self.candidate_implications:
            print(premise)
            new_p = add_counts(premise, p, self.bound)
            new_q = add_counts(conclusion, q, self.bound)
            if self.is_good(new_p, new_q):
                result.append((p, q))
        return result
    
    
    def old_role(self, candidates):
        """
        The implicational role of a set (list) of candidate implications.
        """
        norm = tuple(self._fix_pq(p, q) for (p, q) in candidates)
        if norm in self.roles:
            return self.roles[norm]
        if not norm:
            return []
    
        # First compute the RSR of candidates
        base_rsr = frozenset(self.RSR(candidates))
        to_check = []
        # Then check all other RSRs that contain this RSR. 
        # Since the role is those sets of candidate implications s.t. the intersection
        # of the RSR of their members is equal to RSR of our original thing,
        # we need only check the sets that are comprised of candidates whose RSR contains
        # the RSR of our original thing. If there was a candidate whose RSR didn't contain it,
        # then certainly the intersection of it with other things would not contain it. 
        for p, q in self.candidate_implications:    # for each candidate implication
            cand_rsr = self.RSRs[(p,q)]             # get its RSR
            if base_rsr.issubset(cand_rsr):         # if it contains the RSR of the guy we are checking,
                to_check.append((p, q))             # we need to deal with it.
        print(f"number of candidates to check: {len(to_check)}")
        if len(to_check) > 25:
            print("too many things to check.")
            return None
        role = []                                   # initialize empty role.
        local_rsrs = {pair: self.RSRs[pair] for pair in to_check}   # locally instantiate the RSRs of things we need to deal with
        for subset in powerset_iter(to_check):      # stream the candidate subsets (elements are candidate implications we need to handle), starting with 
            inter = set(local_rsrs[subset[0]])      # start with the local RSR of the first element of the subset.
            for cand in subset[1:]:                 # cumulatively intersect: for each of the next elements of the set,
                inter.intersection_update(local_rsrs[cand])     # take the intersection.
            if inter == base_rsr:
                role.append(subset)  
        self.roles[norm] = role
        return role 

    def pretty_print_role(self, candidates):
        """
        return a human-friendly string representation of the implicational role of `candidates`.
        """
        role_sets = self.role(candidates)
        if role_sets is None:
            return "role too large to compute."
        # helper to label a candidate pair
        def label_pair(pair):
            premise, conclusion = pair
            print(pair)
            print(premise)
            # premise and conclusion are count-tuples
            p = ''.join(b * c for b, c in zip(self.bearers, premise))
            q = ''.join(b * c for b, c in zip(self.bearers, conclusion))
            p_label = p if p else '∅'
            q_label = q if q else '∅'
            return f"{p_label}|~{q_label}"
        # header
        cand_labels = [label_pair((p,q)) for p,q in candidates]
        lines = [f"role of [{', '.join(cand_labels)}]:"]
        # each minimal role subset
        for subset in role_sets:
            labels = [label_pair(pair) for pair in subset]
            lines.append("  {" + ", ".join(labels) + "}")
        return "\n".join(lines)

    #profile
    def role(self, candidates):
        #norm = tuple(self._fix_pq(p, q) for (p, q) in candidates)
        #print(len(norm))
        #if candidates in self.roles:
        #    return self.roles[candidates]
        if not candidates:
            return []
        # First compute the RSR of candidates
        base_rsr = frozenset(self.RSR(candidates))
        to_check = []
        for p, q in self.candidate_implications:
            cand_rsr = self.RSRs[(p, q)]
            if base_rsr.issubset(cand_rsr):
                to_check.append((p, q))
        print(f"number of candidates to check: {len(to_check)}")
        #if len(to_check) > 25:
            #print("too many things to check.")
            #return None
        local_rsrs = {pair: self.RSRs[pair] for pair in to_check}
        edges = []
        # build hyperedges for extra elements
        extras = set().union(*local_rsrs.values()) - base_rsr
        edges = [[c for c, rs in local_rsrs.items() if e not in rs] for e in extras]

        # use PySAT Hitman to compute minimal hitting sets
        # map each candidate to an integer id
        to_check_list = list(local_rsrs.keys())
        hitman = Hitman()
        for edge in edges:
            # convert edge of candidate tuples to clause of positive ids
            clause = [to_check_list.index(c) + 1 for c in edge]
            hitman.hit(clause)

        minimal_roles = []
        # enumerate minimal hitting sets
        for mhs in hitman.enumerate():
            #print(mhs)
            # each mhs is a list of positive integers
            role_set = tuple(to_check_list[idx - 1] for idx in mhs)
            minimal_roles.append(role_set)
        
        # include all supersets of minimal hitting sets
        #from itertools import combinations
        #full_roles = []
        #all_candidates = list(to_check_list)
        #for minimal in minimal_roles:
            # determine extra elements not in this minimal set
            #extras = [c for c in all_candidates if c not in minimal]
            #for each possible inclusion of extra elements (including none)
            #for r in range(len(extras) + 1):
                #for combo in combinations(extras, r):
                    #superset = tuple(minimal) + combo
                    #full_roles.append(superset)
        
        #role = full_roles
        #return role


        self.roles[candidates] = minimal_roles
        return minimal_roles
    
    def bearer_role(self, bearer):
        """
        The implicational role of a bearer, as the tuple consisting of its premisory and conclusory roles.
        """
        return self.premisory_role(bearer), self.conclusory_role(bearer)

    def premisory_role(self, bearer):
        """
        The premisory role of a bearer, i.e. the implicational role of (bearer,∅).
        """
        return self.role([(bearer,"")])
    
    def conclusory_role(self, bearer):
        """
        The conclusory role of a bearer, i.e. the implicational role of (∅,bearer).
        """
        return self.role([("",bearer)])
    
    def symjunction(self, roles):
        return 
    
    def containment(self):
        """
        Check if the base reason relation (implication matrix) obeys Containment.
        """
        for s in self.sets_of_bearers:
            for r in subcounters(s):
                if not self.is_good(s,r):
                    return False
        return True


def main():
    use_def = input("zazzles (z), chocolate (c), all-ones (2), other (N)? (z/N/2) ").strip().lower()
    if use_def == 'z':
        # example for n=2: explicit 4x4 default matrix
        n = 2
        zazzles = [
            [1, 1, 0, 1],
            [0, 1, 0, 1],
            [0, 0, 1, 1],
            [1, 1, 1, 1]
        ]
        f = ImplicationFrame(n, bound=1, example=zazzles)
    elif use_def == '2':
        matrix = matrix = [
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
]
        f = ImplicationFrame(2, bound=2, example=matrix)
    elif use_def == 'c':
        matrix = matrix = [
    [1, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 0, 0, 0, 0, 0, 0],
    [1, 0, 1, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 1, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 1, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1, 0],
    [1, 1, 1, 0, 1, 1, 1, 1, 0],
    [1, 1, 1, 1, 1, 1, 1, 1, 1],
]
        f = ImplicationFrame(2, bound=2, example=matrix)
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


    print(f"containment: {f.containment()}")

    #role = f.role([(Counter({'a':1,'b':1}), "a"),("","b")])

    #print(f"role of [(ab,a),('',b)]: is {len(role)}")
    #for thing in role:
        #print(thing)

    #for (p,q) in f.candidate_implications:
        #role = f.role([(p,q)])
        #if role:
            #print(f"role of {(p,q)}: is {len(role)}")
    


if __name__ == "__main__":
    main()