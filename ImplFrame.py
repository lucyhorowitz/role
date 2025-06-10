from multiset import *
from translate import *
from drhagen.szudzik import *
import itertools

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
    def __init__(self, num_bearers):
        self.num_bearers = num_bearers
        BEARERS = tuple("abcdefghijklmnopqrstuvwxyz"[:num_bearers]) 
        self.bearers = [name for name in BEARERS]
    

class ImplicationFrame(ImplicationSpace):
    def __init__(self, num_bearers, implications, containment=True, reflexivity=True):
        """
        Initialize an implication frame.

        `num_bearers` is the number of bearers that will appear in the implication space/frame. 
        `implications` is a list of implications that you say will hold, formatted as "ab |~ b".
        `containment` is a boolean that determines whether containment implications beyond those specified in `implications` will hold. If there is a containment implication within the "bounds" of implications and `containment` is set to true, that implication will evaluate to `true`. 
        `reflexivity` is a boolean that determines whether reflexive implications beyond those specified in `implications` will hold. If there is a reflexive implication within the "bounds" of implications and `containment` is set to true, that implication will evaluate to `true`. Note that containment implies reflexivity.
        """
        ImplicationSpace.__init__(self, num_bearers)

        self.implications = [implication_to_cindex(imp, self.num_bearers) for imp in implications]

        if containment:
            self.containment = containment
            self.reflexivity = True
        else:
            self.containment = containment
            self.reflexivity = reflexivity

    def is_good(self, candidate):
        if isinstance(candidate, str):
            return self.is_good(implication_to_cindex(candidate))
        elif isinstance(candidate, tuple):
            if self.reflexivity and candidate[0] == candidate[1]: 
                return True
            if self.containment and multi_intersection(index_to_tuple(candidate[0],self.num_bearers),index_to_tuple(candidate[1],self.num_bearers)) != (0,0):
                return True
            else:
                return self.is_good(pair_to_cindex(candidate))
        elif isinstance(candidate, int):
            return candidate in self.implications
        
    def is_by_reflexivity(self, candidate):
        """
        return True if the implication holds by reflexivity rule.
        """
        if isinstance(candidate, tuple):
            return self.reflexivity and candidate[0] == candidate[1]
        raise TypeError("candidate must be a pair of indices")

    def is_by_containment(self, candidate):
        """
        return True if the implication holds by containment rule.
        """
        if isinstance(candidate, tuple):
            tup0 = index_to_tuple(candidate[0], self.num_bearers)
            tup1 = index_to_tuple(candidate[1], self.num_bearers)
            # non-empty multiset intersection
            return self.containment and multi_intersection(tup0, tup1) != (0,) * self.num_bearers
        raise TypeError("candidate must be a pair of indices")

    def pretty(self, bound = 2, padding: int = 0) -> str:
        """
        return a string table of the implication matrix.
        `padding` controls spaces around each cell (default 0).
        """
        # generate all multisets up to bound
        ms = list(itertools.product(range(bound+1), repeat=self.num_bearers))
        labels = [''.join(b*c for b, c in zip(self.bearers, tup)) or '∅' for tup in ms]
        idxs = [tuple_to_index(tup) for tup in ms]
        # sort all headers by length then alphabetically
        triplets = list(zip(ms, labels, idxs))
        triplets.sort(key=lambda x: (len(x[1]), x[1]))
        # ensure the empty multiset comes first
        empty = tuple([0] * self.num_bearers)
        for i, t in enumerate(triplets):
            if t[0] == empty:
                triplets.insert(0, triplets.pop(i))
                break
        ms, labels, idxs = zip(*triplets)
        ms, labels, idxs = list(ms), list(labels), list(idxs)

        # determine cell width
        cell_width = max(max(len(l) for l in labels), 1) + 2 * padding
        # helper to center text
        def center(txt):
            return txt.center(cell_width)

        # symbols for implication reasons
        check_sym = '✔'
        contain_sym = '✓'
        reflex_sym = '◦'

        # build table rows with grid lines
        labels_with_empty = [''] + labels
        border = '+' + '+'.join('-' * cell_width for _ in labels_with_empty) + '+'
        rows = [border]
        header = '|' + '|'.join(center(l) for l in labels_with_empty) + '|'
        rows.append(header)
        rows.append(border)
        for tup, lab, idx in zip(ms, labels, idxs):
            row_cells = [center(lab)]
            for col_idx in idxs:
                candidate = (idx, col_idx)
                # explicit implications take priority
                if pair_to_cindex(candidate) in self.implications:
                    sym = check_sym
                elif self.is_by_reflexivity(candidate):
                    sym = reflex_sym
                elif self.is_by_containment(candidate):
                    sym = contain_sym
                else:
                    sym = ''
                row_cells.append(center(sym))
            row = '|' + '|'.join(row_cells) + '|'
            rows.append(row)
        rows.append(border)
        return '\n'.join(rows)

    def __str__(self):
        return self.pretty()
    
    def __repr__(self):
        return self.pretty()