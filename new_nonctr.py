from itertools import chain, combinations, product
from string import ascii_lowercase
from collections import defaultdict, Counter
import time
from pysat.examples.hitman import Hitman
from pysat.solvers import Solver
import random

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

def sub_multiset(t):
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
        # map each multiset to its index for O(1) lookup
        self.idx = {counts: i for i, counts in enumerate(self.sets_of_bearers)}


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
        if example == "random":
            self.implications = [[None] * size for _ in range(size)]
            for i, A in enumerate(self.sets_of_bearers):
                for j, B in enumerate(self.sets_of_bearers):
                    self.implications[i][j] = random.randint(0,1)
        elif example == "0":
            self.implications = [[None] * size for _ in range(size)]
            for i, A in enumerate(self.sets_of_bearers):
                for j, B in enumerate(self.sets_of_bearers):
                    self.implications[i][j] = 0
        elif example == "1":
            self.implications = [[None] * size for _ in range(size)]
            for i, A in enumerate(self.sets_of_bearers):
                for j, B in enumerate(self.sets_of_bearers):
                    self.implications[i][j] = 1
        elif example is not None:
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
        self.RSRs, self.atomic_roles, self.roles = {}, {}, {}
        for (p, q) in self.candidate_implications:
            self.RSRs[(p, q)] = self._RSR(p, q)
        
        for (p, q) in self.candidate_implications:
            role = self.role(((p, q)))
            self.atomic_roles[(p, q)] = role
            self.roles[(p, q)] = role

    def __repr__(self):
        return self.pretty()
    
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

    def is_good(self, premise, conclusion):
        """
        Check whether a candidate implication is good (1) or not (0).
        
        `premise` and `conclusion` should each be tuples representing the number of times each bearer is appearing.
        For example, if there are 2 bearers and the "bound" is 2, then we could have something like `premise = (1,2)` for a,b,b.
        """
        # lookup indices in O(1) using the idx map
        try:
            p_index = self.idx[premise]
        except KeyError:
            raise ValueError(f"premise {premise} not in this implication frame")
        try:
            c_index = self.idx[conclusion]
        except KeyError:
            raise ValueError(f"conclusion {conclusion} not in this implication frame")
        return self.implications[p_index][c_index]
    
    def RSR(self, candidates):
        """
        intersection of the RSRs for each (premise, conclusion) in `candidates`.

        `candidates` is a tuple of pairs. Each pair is a pair of tuples tuples representing the number of 
        times each bearer is appearing. For example, if there are 2 bearers and the "bound" is 2, then we could 
        have something like ((1,1),(0,0)) for a,b |~ ∅
        """
        if candidates in self.RSRs:
            return self.RSRs[candidates]
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
        """
        An internal helper method for computing the RSR of a single candidate implication. As usual, premise
        and conclusion are both tuples representing multisets of bearers.
        """
        if (premise,conclusion) in self.RSRs:
            return self.RSRs[(premise,conclusion)]
        result = []
        for (p,q) in self.candidate_implications:
            new_p = add_counts(premise, p, self.bound)
            new_q = add_counts(conclusion, q, self.bound)
            if self.is_good(new_p, new_q):
                result.append((p, q))
        return result
    
    def role(self, candidates):
        """
        Compute the role of a tuple of `candidates` where each candidate is a pair of tuples, and the
        tuples represent multisets of bearers.

        It returns `minimals`, which is a collection of sets of candidate implications, and `to_check`,
        which is the set of candidate implications in which to take the upward closure of all of the `minimals`
        in order to get the full role (set of things which share an RSR.)
        """
        if candidates in self.roles:
            return self.roles[candidates]
        if not candidates:
            return []
        
        base_rsr = frozenset(self.RSR(candidates))
        to_check = []
        for p, q in self.candidate_implications:
            cand_rsr = self.RSRs[(p, q)]
            if base_rsr.issubset(cand_rsr):
                to_check.append((p, q))
        local_rsrs = {pair: self.RSRs[pair] for pair in to_check}
        edges = []

        extras = set().union(*local_rsrs.values()) - base_rsr
        edges = [[c for c, rs in local_rsrs.items() if e not in rs] for e in extras]

        # use PySAT Hitman to compute minimal hitting sets
        to_check_list = list(local_rsrs.keys())
        hitman = Hitman()
        for edge in edges:
            clause = [to_check_list.index(c) + 1 for c in edge]
            hitman.hit(clause)

        minimals = []
        # enumerate minimal hitting sets
        i = 1
        for mhs in hitman.enumerate():
            #print(mhs)
            # each mhs is a list of positive integers
            role_set = tuple(to_check_list[idx - 1] for idx in mhs)
            i += 1 
            minimals.append(role_set)

        return (minimals, to_check)

    def containment(self):
        """
        Check if the base reason relation (implication matrix) obeys Containment.
        """
        for s in self.sets_of_bearers:
            for r in sub_multiset(s):
                if not self.is_good(s,r):
                    return False
        return True
    
    def adjunction(self, roles):
        """
        adjunction of implicational roles: given a list of roles (minimals, to_check),
        form all combined candidates by summing premises and conclusions of one candidate
        from each role (caps at bound), and return the role of that set.
        """
        # collect lists of candidate implications
        candidate_lists = [to_check for (_min, to_check) in roles]
        # form all unions (multiset sums) of one candidate from each role
        combined = []
        for combo in product(*candidate_lists):
            # start with first
            p_sum, q_sum = combo[0]
            # accumulate sums with clipping
            for (p, q) in combo[1:]:
                p_sum = add_counts(p_sum, p, self.bound)
                q_sum = add_counts(q_sum, q, self.bound)
            combined.append((p_sum, q_sum))
        # return the role of the adjunction set
        return self.role(tuple(combined))



    
    def symjunction(self, roles):
        """
        Given a list of `roles`, which are tuples (minimals, to_check), we factor the roles, then
        take the role of the union of the factors. 
        """
        candidates = []
        for (minimals, to_check) in roles:
            if minimals:
                rsr = self.RSR(minimals[0])
            else:
                rsr = self.RSR(to_check[0])
            factored = self.factor(rsr)
            # add each candidate from this factor
            for factor in factored:
                for cand in factor:
                    candidates.append(cand)
        
        return self.role(tuple(candidates))


    # (removed stub method factor(self, role))
            
    def pretty_print_role(self, candidates):
        """
        pretty-print role sets: candidates is a list of tuples of candidate pairs.
        """
        labels = self._subset_labels()
        label_map = {counts: lbl for counts, lbl in zip(self.sets_of_bearers, labels)}
        if not candidates:
            return "∅"
        to_print = []
        for role_set in candidates:
            elems = [f"{label_map[p]} |~ {label_map[q]}" for p, q in role_set]
            to_print.append("{" + ", ".join(elems) + "}")
        return to_print

    def pretty_print_rsr(self, rsr_list):
        """
        pretty-print an rsr list of candidate implications: rsr_list is a list of (premise, conclusion) tuples.
        """
        labels = self._subset_labels()
        label_map = {counts: lbl for counts, lbl in zip(self.sets_of_bearers, labels)}
        if not rsr_list:
            print("∅")
            return
        elems = [f"{label_map[p]} |~ {label_map[q]}" for p, q in rsr_list]
        return "{" + ", ".join(elems) + "}"

    def pretty_print_implication(self, candidate):
        """
        pretty-print a single candidate implication: implication is a tuple (premise, conclusion).
        """
        labels = self._subset_labels()
        label_map = {counts: lbl for counts, lbl in zip(self.sets_of_bearers, labels)}
        p, q = candidate
        prem_label = label_map.get(p, str(p))
        concl_label = label_map.get(q, str(q))
        return f"{prem_label} |~ {concl_label}"

    def back_translate_implication(self, s: str):
        """
        parse a pretty-printed implication string "label1 |~ label2" into a candidate implication tuple.
        """
        s = s.strip()
        # remove surrounding braces if present
        if s.startswith("{") and s.endswith("}"):
            s = s[1:-1].strip()
        parts = [part.strip() for part in s.split("|~")]
        if len(parts) != 2:
            raise ValueError(f"invalid implication format: {s}")
        prem_label, concl_label = parts
        labels = self._subset_labels()
        rev_map = {lbl: counts for counts, lbl in zip(self.sets_of_bearers, labels)}
        try:
            return (rev_map[prem_label], rev_map[concl_label])
        except KeyError as e:
            raise ValueError(f"unknown label: {e.args[0]}")

    def is_role_subset(self, role1, role2):
        """
        check if role1 (list of minimal role tuples) is subset of role2.
        returns True if every minimal role in role1 has a superset in role2.
        """
        for r in role1:
            rset = set(r)
            if not any(rset.issubset(set(s)) for s in role2):
                return False
        return True

    def factor(self, rsr):
        # factor an RSR into atomic RSRs if possible
        base_rsr = frozenset(rsr)
        # check for atomic match
        for cand, rs in self.RSRs.items():
            if frozenset(rs) == base_rsr:
                return [(cand,)]
        # collect candidates whose RSRs cover base_rsr
        to_check = [cand for cand, rs in self.RSRs.items() if base_rsr.issubset(rs)]
        # if no candidates cover base, error
        if not to_check:
            raise ValueError(f"cannot factor RSR: {rsr}")
        # prepare local RSR sets
        local_rsrs = {cand: frozenset(self.RSRs[cand]) for cand in to_check}
        # compute extras beyond base
        extras = set().union(*local_rsrs.values()) - base_rsr
        # build hitting set clauses
        hitman = Hitman()
        to_check_list = to_check
        for e in extras:
            # candidates missing e
            clause = [to_check_list.index(cand) + 1 for cand, rs in local_rsrs.items() if e not in rs]
            hitman.hit(clause)
        # enumerate minimal factor sets
        factors = []
        for mhs in hitman.enumerate():
            factor_set = tuple(to_check_list[idx - 1] for idx in mhs)
            factors.append(factor_set)
        if not factors:
            raise ValueError(f"cannot factor RSR: {rsr}")
        return factors