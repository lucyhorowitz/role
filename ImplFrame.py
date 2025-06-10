from multiset import *
from translate import *
from drhagen.szudzik import *

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

        self.implications = [implication_to_cindex(imp) for imp in implications]

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
            if self.containment and multi_intersection(index_to_tuple(candidate[0]),index_to_tuple(candidate[1])) != (0,0):
                return True
            else:
                return self.is_good(pair_to_cindex(candidate))
        elif isinstance(candidate, int):
            return candidate in self.implications
        

    
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
    
    def __repr__(self):
        return self.pretty()