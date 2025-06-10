from drhagen.general import Count
from functools import reduce
from itertools import count
from operator import mul
from typing import Iterable
from drhagen.szudzik import multidimensional_szudzik_pairing, multidimensional_szudzik_unpairing, multidimensional_szudzik_product
from ImplFrame import string_to_tuple
from translate import *


def assert_md_consistency(product, pairing, unpairing):
    dims = 4
    for dim in range(1, dims+1):
        iterables = [Count()] * dim
        for i, elements in zip(range(100), product(*iterables)):
            paired = pairing(*elements)
            unpaired = unpairing(dim, i)
            print(f'{i} == {paired}, {elements} == {unpaired}')
            assert i == paired
            assert elements == unpaired



if __name__ == "__main__":
    # "abb" -> (1,2) -> 5
    # "b"   -> (0,1) -> 1
    # "abb |~ b" -> (5,1) -> ?
    things1 = []
    things2 = []
    for i in range (0,1000):
        #print(f"{pair_to_implication((i,i),2)} : {pair_to_cindex((i,i))}")
        things1.append(pair_to_cindex((i,i)))

    for i in range (0,1000):
        #print(f"{pair_to_implication((i,i),3)} : {pair_to_cindex((i,i))}")
        things2.append(pair_to_cindex((i,i)))
    
    print(things1 == things2)