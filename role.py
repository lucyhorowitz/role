from itertools import chain, combinations
from string import ascii_lowercase
from collections import defaultdict, Counter

#todos: add checks for monotonicity, etc.
#       go through all of the things and decide on the types for the implications: tuples sets?
#       generalize to multisets(?)

def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

class Bearer:
    def __init__(self, name):
        self.name = name
        
    def __str__(self):
        return self.name
    
class ImplicationSpace:
    def __init__(self, num_bearers):
        self.num_bearers = num_bearers
        self.bearers = [Bearer(name) for name in ascii_lowercase[:num_bearers]]
        ps = list(powerset(self.bearers))
        self.candidate_implications = [(a, b) for a in ps for b in ps]

class ImplicationFrame(ImplicationSpace):
    def __init__(self, num_bearers, set_example=None,compute_now=False):
        ImplicationSpace.__init__(self, num_bearers)

        # enumerate all subsets of bearers
        self.subsets = [set(s) for s in powerset(self.bearers)]
        size = len(self.subsets)

        if set_example is not None:
            self.implications = set_example
            return

        # initialise implication matrix with None
        self.implications = [[None] * size for _ in range(size)]

        # default ones: non‑empty intersection or both empty
        for i, A in enumerate(self.subsets):
            for j, B in enumerate(self.subsets):
                if (not A and not B) or (set(A) & set(B)):
                    self.implications[i][j] = 1

        # prompt user for remaining entries
        for i, A in enumerate(self.subsets):
            for j, B in enumerate(self.subsets):
                if self.implications[i][j] is None:
                    while True:
                        a_label = '∅' if not A else '{' + ','.join(b.name for b in A) + '}'
                        b_label = '∅' if not B else '{' + ','.join(b.name for b in B) + '}'
                        ans = input(f"{a_label} |~ {b_label} ? (0/1): ").strip()
                        if ans in {"0", "1"}:
                            self.implications[i][j] = int(ans)
                            break
                        print("please enter 0 or 1")

        if compute_now:
            # Compute roles: group candidate implications by their RSR
            self.roles = defaultdict(set)
            sets = powerset(self.candidate_implications)

    def __getitem__(self, key):
        i, j = key
        return self.implications[i][j]

    def __repr__(self):
        return self.pretty()

    # pretty‑print the implication matrix with subset labels
    def _subset_labels(self):
        """internal helper: human‑friendly labels for each subset"""
        return ['∅' if not s else ','.join(b.name for b in s) for s in self.subsets]

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
        """Check whether a given implication is good (1) or not (0)."""
        # convert list of string names to bearer objects
        name_to_bearer = {b.name: b for b in self.bearers}
        try:
            A = set(name_to_bearer[name] for name in premise)
            B = set(name_to_bearer[name] for name in conclusion)
        except KeyError as e:
            raise ValueError(f"unknown bearer name: {e.args[0]}")

        i = self.subsets.index(A)
        j = self.subsets.index(B)
        return self.implications[i][j]
    
    def RSR(self, candidates, pretty_print=False):
        if not isinstance(candidates, list) or isinstance(candidates, set):
            raise TypeError("candidates must be a list/set of candidate implications")
        for c in candidates:
            if not (isinstance(c, tuple) and len(c) == 2):
                raise ValueError("each candidate must be a tuple (A, B)")
        result_sets = []
        for premise, conclusion in candidates:
            result_sets.append(set(self._RSR(premise, conclusion)))
        if not result_sets:
            return set()
        intersection = set.intersection(*result_sets)
        if pretty_print:
            ret = []
            for A, B in intersection:
                a_label = '∅' if not A else '{' + ','.join(b.name for b in A) + '}'
                b_label = '∅' if not B else '{' + ','.join(b.name for b in B) + '}'
                ret.append(f"({a_label}, {b_label})")
            return ",".join(ret)
        return intersection
        
    def _RSR(self, premise, conclusion):
        """Return all candidate (a,b) such that is_good(p + a, q + b)."""
        name_to_bearer = {b.name: b for b in self.bearers}
        try:
            P = tuple(name_to_bearer[name] for name in premise)
            Q = tuple(name_to_bearer[name] for name in conclusion)
        except KeyError as e:
            raise ValueError(f"unknown bearer name: {e.args[0]}")

        results = []
        for A, B in self.candidate_implications:
            union_p = list(P) + list(A)
            union_q = list(Q) + list(B)
            if self.is_good([b.name for b in set(union_p)], [b.name for b in set(union_q)]):
                results.append((A, B))
        return results
    
    def premisory_role(self, a, pretty_print=False):
        return self.RSR([(a,"")],pretty_print)
    
    def conclusory_role(self, a, pretty_print=False):
        return self.RSR([("",a)],pretty_print)
    
    def role(self, candidates, pretty_print=False):
        if not isinstance(candidates, list) or isinstance(candidates, set) or isinstance(candidates,Bearer):
            raise TypeError("candidates must be a list/set of candidate implications or a bearer")
        if isinstance(candidates, Bearer):
            return (self.premisory_role(candidates,pretty_print),self.conclusory_role(candidates,pretty_print))
        for c in candidates:
            if not (isinstance(c, tuple) and len(c) == 2):
                raise ValueError("each candidate must be a tuple (A, B)")
            
        # Return all candidate implications with the same RSR as the input candidates
        target = self.RSR(candidates)
        all_candidates = list(self.candidate_implications)
        result = set()
        for cand in all_candidates:
            if self.RSR([cand]) == target:
                result.add(cand)
        if pretty_print:
            ret = []
            for A, B in result:
                a_label = '∅' if not A else '{' + ','.join(b.name for b in A) + '}'
                b_label = '∅' if not B else '{' + ','.join(b.name for b in B) + '}'
                ret.append(f"({a_label}, {b_label})")
            return ",".join(ret)
        return result
    
    def adjunction(self, role_1, role_2):


def main():
    use_def = input("use default Zazzles example? (y/N) ").strip().lower()
    if use_def == 'y':
        # example for n=2: explicit 4x4 default matrix
        n = 2
        default = [
            [1, 1, 0, 1],
            [0, 1, 0, 1],
            [0, 0, 1, 1],
            [1, 1, 1, 1]
        ]
        f = ImplicationFrame(n, set_example=default)
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
        f = ImplicationFrame(n)

    print("\nimplication matrix:\n")
    print(f)

    # Pretty-print all possible RSRs
    print("\nAll possible RSRs:")
    all_candidates = list(f.candidate_implications)
    for premise, conclusion in all_candidates:
        a_label = '∅' if not premise else '{' + ','.join(b.name for b in premise) + '}'
        b_label = '∅' if not conclusion else '{' + ','.join(b.name for b in conclusion) + '}'
        rsr_pretty = f.RSR([(tuple(b.name for b in premise), tuple(b.name for b in conclusion))], pretty_print=True)
        print(f"RSR({a_label} |~ {b_label}): {rsr_pretty}")

    # Group candidate implications by their RSR

    rsr_groups = defaultdict(list)
    for premise, conclusion in all_candidates:
        key = f.RSR([(tuple(b.name for b in premise), tuple(b.name for b in conclusion))])
        rsr_groups[frozenset(key)].append((premise, conclusion))

    print("\nGroups of candidate implications with the same RSR:")
    for group, implications in rsr_groups.items():
        if len(implications) > 1:
            labels = []
            for premise, conclusion in implications:
                a_label = '∅' if not premise else '{' + ','.join(b.name for b in premise) + '}'
                b_label = '∅' if not conclusion else '{' + ','.join(b.name for b in conclusion) + '}'
                labels.append(f"{a_label} |~ {b_label}")
            print(", ".join(labels))
    

if __name__ == "__main__":
    main()