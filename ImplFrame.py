from multiset import *
from translate import *
from drhagen.szudzik import *
import itertools
import math

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
    def __init__(self, num_bearers, implications, containment=False, reflexivity=True):
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
        A good fact is that the reflexive indices are of the form `n^2 + (2 * n)`.
        """
        if isinstance(candidate, tuple):
            return self.reflexivity and candidate[0] == candidate[1] and candidate not in self.implications
        if isinstance(candidate, int):
            if self.reflexivity and candidate not in self.implications:
                k = candidate
                s = math.isqrt(k + 1)
                return s*s == k + 1 and s - 1 >= 0
        if isinstance(candidate, str):
            return self.is_by_reflexivity(implication_to_pair(candidate,self.num_bearers))

    def is_by_containment(self, candidate):
        """
        return True if the implication holds by containment rule.
        """
        if isinstance(candidate, tuple):
            tup0 = index_to_tuple(candidate[0], self.num_bearers)
            tup1 = index_to_tuple(candidate[1], self.num_bearers)
            # non-empty multiset intersection
            return self.containment and multi_intersection(tup0, tup1) != (0,) * self.num_bearers
        if isinstance(candidate, str):
            return self.is_by_containment(implication_to_pair(candidate,self.num_bearers))
        if isinstance(candidate, int):
            return self.is_by_containment(cindex_to_pair(candidate))
    
    def otimes(self, rsr1, rsr2):
        exp_rsr1, imp_rsr1 = rsr1
        exp_rsr2, imp_rsr2 = rsr2
        
        new_exp = self.add_sets(exp_rsr1, exp_rsr2)

        if not imp_rsr1 and not imp_rsr2:
            return new_exp, set()
        elif not imp_rsr1:
            temp_imp = self.add_sets(exp_rsr1, imp_rsr2)
            new_imp = {imp for imp in temp_imp if self.reduce_implication(imp) == imp}
            for imp in temp_imp:
                reduced = self.reduce_implication(imp)
                if reduced != imp and reduced not in new_imp:
                    new_imp.add(imp)
            return new_exp, self.minimal_by_reflexive_path(new_imp)
        elif not imp_rsr2:
            temp_imp = self.add_sets(imp_rsr1, exp_rsr2)
            new_imp = {imp for imp in temp_imp if self.reduce_implication(imp) == imp}
            for imp in temp_imp:
                reduced = self.reduce_implication(imp)
                if reduced != imp and reduced not in new_imp:
                    new_imp.add(imp)
            return new_exp, self.minimal_by_reflexive_path(new_imp)
        elif imp_rsr1 and imp_rsr2:
            temp_imp = self.add_sets(exp_rsr1, imp_rsr2).union(self.add_sets(imp_rsr1, exp_rsr2).union(self.add_sets(imp_rsr1, imp_rsr2)))
            new_imp = {imp for imp in temp_imp if self.reduce_implication(imp) == imp}
            for imp in temp_imp:
                reduced = self.reduce_implication(imp)
                if reduced != imp and reduced not in new_imp:
                    new_imp.add(imp)
            return new_exp, self.minimal_by_reflexive_path(new_imp)
        
    #@profile   
    def add_sets(self, set1, set2):
            new_set = set()
            set_pairs_1, set_pairs_2 = [cindex_to_pair(cand) for cand in set1], [cindex_to_pair(cand) for cand in set2]
            for pair1 in set_pairs_1:
                for pair2 in set_pairs_2:
                    p1, q1 = index_to_tuple(pair1[0], self.num_bearers), index_to_tuple(pair1[1], self.num_bearers)
                    p2, q2 = index_to_tuple(pair2[0], self.num_bearers), index_to_tuple(pair2[1], self.num_bearers)
                    new_p = tuple(a+b for a,b in zip(p1, p2))
                    new_q = tuple(a+b for a,b in zip(q1, q2))
                    new_set.add(pair_to_cindex((tuple_to_index(new_p),tuple_to_index(new_q))))
            return new_set
    
    def minimal_by_reflexive_path(self, imps):
        """
        return a set of implications in imps that have no reflexive sub-part yielding another element in imps.
        """
        # generate all reflexive implications up to the max tuple size in imps
        # determine max multiset size among all implications
        max_len = 0
        for cand in imps:
            p_idx, q_idx = cindex_to_pair(cand)
            p = index_to_tuple(p_idx, self.num_bearers)
            q = index_to_tuple(q_idx, self.num_bearers)
            max_len = max(max_len, sum(p), sum(q))
        # build reflexive set: all t|~t with sum(counts) <= max_len
        reflexives = set()
        for counts in product(range(max_len+1), repeat=self.num_bearers):
            if sum(counts) <= max_len:
                idx = pair_to_cindex((tuple_to_index(counts), tuple_to_index(counts)))
                reflexives.add(idx)
        # remove the empty reflexive implication (all-zero multiset)
        reflexives.discard(0)
        minimal_set = set()
        
        for cand in imps:
            exclude = False
            for r in reflexives:
                # subtract reflexive part r from cand
                cp = cindex_to_pair(cand)
                rp = cindex_to_pair(r)
                p_cand = index_to_tuple(cp[0], self.num_bearers)
                q_cand = index_to_tuple(cp[1], self.num_bearers)
                p_ref = index_to_tuple(rp[0], self.num_bearers)
                if any(pr > pc for pc, pr in zip(p_cand, p_ref)) or any(pr > qc for qc, pr in zip(q_cand, p_ref)):
                    continue
                new_p = tuple(pc - pr for pc, pr in zip(p_cand, p_ref))
                new_q = tuple(qc - pr for qc, pr in zip(q_cand, p_ref))
                new_idx = pair_to_cindex((tuple_to_index(new_p), tuple_to_index(new_q)))
                if new_idx in imps:
                    exclude = True
                    break

            if not exclude:
                minimal_set.add(cand)
        return minimal_set
    
    def reduce_implication(self, candidate):
        if isinstance(candidate, str):
            return self.reduce_implication(implication_to_pair(candidate, self.num_bearers))
        if isinstance(candidate, int):
            # convert cindex to pair
            return self.reduce_implication(cindex_to_pair(candidate))
        if isinstance(candidate, tuple):
            # remove common bearers from both sides
            p_idx, q_idx = candidate
            p = index_to_tuple(p_idx, self.num_bearers)
            q = index_to_tuple(q_idx, self.num_bearers)
            # compute reduced sides by subtracting the multiset intersection
            common = tuple(min(pi, qi) for pi, qi in zip(p, q))
            new_p = tuple(pi - ci for pi, ci in zip(p, common))
            new_q = tuple(qi - ci for qi, ci in zip(q, common))
            return pair_to_cindex((tuple_to_index(new_p), tuple_to_index(new_q)))
               
    def RSR(self, candidates):
        """
        Compute the RSR of either: 
        a single candidate implication, represented as either a pair, string, or cindex 
        OR 
        a set of candidate implications, represented as a tuple (exp,imp) where exp and imp are both sets of pairs, strings, or cindices. 
        """
        if self.containment:
            print("RSR for stronger-than-reflexive not implemented yet")
            return
        if isinstance(candidates, str) or isinstance(candidates, int):
            return self._RSR(candidates)
        if isinstance(candidates, tuple) and not isinstance(candidates[0], set):
            return self._RSR(candidates)      
        else:
            # In this case, candidates is (exp, imp). Recall from the Vault that we need to compute the intersection of RC(c) x R for each c in the union of the two sets.
            exp, imp = candidates
            rcs = [self.reflexive_completant(e) for e in exp | imp]
            it = iter(rcs)
            acc = next(it)
            for x in it:
                acc = self.intersection(acc, x)
                if not acc:
                    return (set(),set())
            imp = set()
            imp.add(acc)
            return (set(), imp)

    def intersection(self, c1, c2):
        if self.subpart(c1, c2):
            return c2
        if self.subpart(c2, c1):
            return c1
        if self.is_refl(c1) and self.is_refl(c2):
            t1 = self.tupify(c1)
            t2 = self.tupify(c2)
            summed = tuple(a + b for a, b in zip(t1[0], t2[0]))
            return pair_to_cindex((tuple_to_index(summed), tuple_to_index(summed)))
        if not self.is_refl(c1) and not self.is_refl(c2):
            c1dag = self.non_reflexive_subpart(c1)
            c2dag = self.non_reflexive_subpart(c2)
            if c1dag == c2dag and c1dag is not None:
                t1 = self.tupify(c1)
                t2 = self.tupify(c2)
                print(t1)
                print(t2)
                max_1 = tuple(max(a, b) for a, b in zip(t1[0], t2[0]))
                max_2 = tuple(max(a, b) for a, b in zip(t1[1], t2[1]))
                # return the reflexive implication whose multiset is the coordinate‑wise max
                return pair_to_cindex((tuple_to_index(max_1), tuple_to_index(max_2)))
        return None

    def leq(self, a, b):
        """
        Check if the difference b - a of the tuples (bearer multisets) a and b is well-defined.
        In the event that this returns True, a is a subpart of b.
        """
        return all(bi - ai >= 0 for ai, bi in zip(a, b)) 
        
    def tupify(self, c):
        if isinstance(c, int):
            p_idx, q_idx = cindex_to_pair(c)
        elif isinstance(c, str):
            p_idx, q_idx = implication_to_pair(c, self.num_bearers)
        else:
            p_idx = c[0] 
            q_idx = c[1]
        return (index_to_tuple(p_idx, self.num_bearers), index_to_tuple(q_idx, self.num_bearers))
        
    def subpart(self, p, q):
        if isinstance(p, int):
            if isinstance(q,int):
                return self.subpart(cindex_to_pair(p),cindex_to_pair(q))
            if isinstance(q, str):
                return self.subpart(cindex_to_pair(p), implication_to_pair(q, self.num_bearers))
            if isinstance(q,tuple):
                return self.subpart(cindex_to_pair(p), q)
        if isinstance(p,str):
            if isinstance(q,int):
                return self.subpart(implication_to_pair(p, self.num_bearers), cindex_to_pair(q))
            if isinstance(q, str):
                return self.subpart(implication_to_pair(p, self.num_bearers), implication_to_pair(q, self.num_bearers))
            if isinstance(q,tuple):
                return self.subpart(implication_to_pair(p, self.num_bearers), q)
        if isinstance(p, tuple):
            if isinstance(q,int):
                return self.subpart(p, cindex_to_pair(q))
            if isinstance(q, str):
                return self.subpart(p, implication_to_pair(q, self.num_bearers))
            if isinstance(q,tuple):
                p = self.tupify(p)
                q = self.tupify(q)
                return self.leq(p[0], q[0]) and self.leq(p[1], q[1])

    def non_reflexive_subpart(self, p):
        """
        return the *non‑reflexive* remainder of an implication after stripping its
        largest reflexive sub‑part (i.e. the multiset intersection of both sides).

        the remainder is returned as a cindex.  
        if removing the reflexive part yields a reflexive/empty implication,
        we return ``None`` to signal that no proper non‑reflexive sub‑part exists.

        accepts the usual formats: string, cindex int, or pair of idxs.
        """
        if isinstance(p, str):
            return self.non_reflexive_subpart(implication_to_pair(p, self.num_bearers))
        if isinstance(p, int):
            return self.non_reflexive_subpart(cindex_to_pair(p))
        if not isinstance(p, tuple) or len(p) != 2:
            raise TypeError("expected implication as str, int cindex, or (idx,idx) tuple")

        p_idx, q_idx = p
        p_vec = index_to_tuple(p_idx, self.num_bearers)
        q_vec = index_to_tuple(q_idx, self.num_bearers)

        # largest reflexive sub‑part is the coordinate‑wise min
        common = tuple(min(pi, qi) for pi, qi in zip(p_vec, q_vec))

        # subtract the reflexive component
        new_p = tuple(pi - ci for pi, ci in zip(p_vec, common))
        new_q = tuple(qi - ci for qi, ci in zip(q_vec, common))

        # if nothing non‑reflexive remains, signal with None
        if new_p == new_q:
            return None

        return pair_to_cindex((tuple_to_index(new_p), tuple_to_index(new_q)))

    def _RSR(self, candidate):
        if isinstance(candidate, str):
            return self._RSR(implication_to_pair(candidate, self.num_bearers))
        if isinstance(candidate, int):
            return self._RSR(cindex_to_pair(candidate))
        if isinstance(candidate, tuple) and len(candidate) == 2:
            exp_rsr = set()
            imp_rsr = set()
            p, q = index_to_tuple(candidate[0], self.num_bearers), index_to_tuple(candidate[1], self.num_bearers)
            for imp in self.implications:
                temp = cindex_to_pair(imp)
                r, s = index_to_tuple(temp[0], self.num_bearers), index_to_tuple(temp[1],self.num_bearers)
                if all(y_i - x_i >= 0 for x_i, y_i in zip(p, r)) and all(y_i - x_i >= 0 for x_i, y_i in zip(q, s)):
                    new_p = tuple(y_i - x_i for x_i, y_i in zip(p, r))
                    new_q = tuple(y_i - x_i for x_i, y_i in zip(q, s))
                    exp_rsr.add(pair_to_cindex((tuple_to_index(new_p), tuple_to_index(new_q))))
            if self.reflexivity:
                imp_rsr.add(self.reflexive_completant(candidate))
        return (exp_rsr, imp_rsr)
            
    def reflexive_completant(self, candidate):
        if isinstance(candidate, int):
            return self.reflexive_completant(cindex_to_pair(candidate))
        if isinstance(candidate, str):
            return self.reflexive_completant(implication_to_pair(candidate,self.num_bearers))
        if isinstance(candidate, tuple):
            p, q = index_to_tuple(candidate[0], self.num_bearers), index_to_tuple(candidate[1], self.num_bearers)
            new_p = tuple(max(q_i - p_i, 0) for p_i, q_i in zip(p, q))
            new_q = tuple(max(p_i - q_i, 0) for p_i, q_i in zip(p, q))
            return pair_to_cindex((tuple_to_index(new_p), tuple_to_index(new_q)))
    
    def is_refl(self, candidate):
        """
        Checks if a candidate implication is reflexive or not
        """
        if isinstance(candidate,str):
            return self.is_refl(implication_to_cindex(candidate))
        if isinstance(candidate, tuple):
            return candidate[0] == candidate[1]
        if isinstance(candidate, int):
            return self.is_refl(cindex_to_pair(candidate))

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
        reflex_sym = '✓'
        contain_sym = '◦'

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
