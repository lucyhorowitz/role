from drhagen.szudzik import *
from drhagen.general import *

# In this file, the following conventions are followed:
#   "string" refers to a string representing a multiset of bearers.
#   "tuple" refers to a tuple representing a multiset of bearers.
#   "index" refers to an integer index representing a multiset of bearers.
#   "implication" refers to a string representing a candidate implication.
#   "pair" refers to a pair (size-2 tuple) of indices which represents a candidate implication.
#   "cindex" refers to an integer index representing a candidate implication. 

def string_to_tuple(s, num_bearers):
    """
    Converts a string of bearers (unordered) to a tuple representing it as a multiset, 
    e.g. `"abb" -> (1,2)` when `num_bearers = 2`.
    """
    if s == '∅':
        return tuple([0] * num_bearers)
    counts = [0] * num_bearers
    for ch in s:
        if not ('a' <= ch <= chr(ord('a') + num_bearers - 1)):
            raise ValueError(f"invalid bearer: {ch}")
        idx = ord(ch) - ord('a')
        counts[idx] += 1
    return tuple(counts)

def tuple_to_string(tup):
    """
    Converts a tuple representing a multiset of bearers to a string of bearers,
    e.g. `(1,2) -> "abb"`.
    """
    if all(x == 0 for x in tup):
        return '∅'
    s = []
    for i, count in enumerate(tup):
        s.append(chr(ord('a') + i) * count)
    return ''.join(s)

def tuple_to_index(tup):
    """
    Converts a tuple representing a multiset of bearers to an integer index according to the pairing function,
    e.g. `(1,2) -> 5`
    """
    return multidimensional_szudzik_pairing(*tup)

def string_to_index(s, num_bearers):
    """
    Converts a string representing a multiset of bearers to an integer index according to the pairing function,
    e,g. `"abb" -> 5` when `num_bearers = 2`.
    """
    return  multidimensional_szudzik_pairing(*string_to_tuple(s, num_bearers))

def index_to_tuple(i, num_bearers):
    """
    Converts an integer index to a tuple representing a multiset of bearers according to the unpairing function,
    e.g. `5 -> (1, 2)` when `num_bearers = 2`.
    """
    return tuple(multidimensional_szudzik_unpairing(num_bearers, i))

def index_to_string(i, num_bearers):
    """
    Converts an integer index to a string representing a multiset of bearers,
    e.g. `5 -> "abb"` when `num_bearers = 2`.
    """
    return tuple_to_string(index_to_tuple(i, num_bearers))

def implication_to_pair(s, num_bearers):
    """
    Converts a candidate implication to a pair of indices,
    e.g. `"abb |~ b" -> (5,1)` when `num_bearers = 2`.
    """
    if '|~' not in s:
        raise ValueError("implication must be of form 'LHS |~ RHS'")
    lhs, rhs = s.split('|~')
    lhs = lhs.strip()
    rhs = rhs.strip()
    return (tuple_to_index(string_to_tuple(lhs, num_bearers)), tuple_to_index(string_to_tuple(rhs, num_bearers)))

def pair_to_implication(pair, num_bearers):
    """
    Converts a pair of tuples of indices to a candidate implication string,
    e.g. `(5, 1) -> "abb |~ b"`
    """
    lhs, rhs = pair
    return f"{index_to_string(lhs, num_bearers)} |~ {index_to_string(rhs, num_bearers)}"

def pair_to_cindex(pair):
    """
    Converts a pair to a cindex,
    e.g. `(5,1) -> 31`
    """
    return multidimensional_szudzik_pairing(*pair)

def cindex_to_pair(i):
    """
    Converts a cindex to a pair of integer indices using the unpairing function,
    e.g. `31 -> (5, 1)`.
    """
    return tuple(multidimensional_szudzik_unpairing(2, i))

def implication_to_cindex(s, num_bearers):
    """
    Converts a candidate implication string to a cindex according to the pairing functions,
    e.g. `"abb |~ b" -> 31` when `num_bearers = 2`.
    """
    return pair_to_cindex(implication_to_pair(s, num_bearers))

def cindex_to_implication(i, num_bearers):
    """
    Converts a cindex back to a candidate implication string,
    e.g. `31 -> "abb |~ b"` when `num_bearers = 2`.
    """
    return pair_to_implication(cindex_to_pair(i), num_bearers)