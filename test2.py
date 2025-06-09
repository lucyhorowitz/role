from new_nonctr import ImplicationFrame, powerset_iter
from collections import defaultdict, Counter
import time

def main():
    matrix1 = [
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0, 0, 0, 0, 0],
        [1, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 1, 0, 1, 0, 0, 0],
        [0, 0, 0, 1, 1, 1, 0, 0, 0],
        [1, 0, 1, 0, 0, 1, 0, 0, 0],
        [0, 1, 0, 1, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 1, 0, 1, 1, 0],
        [0, 0, 0, 0, 1, 0, 0, 1, 1],
    ]

    matrix2 = [
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
    zazzles = [
            [1, 1, 0, 1],
            [0, 1, 0, 1],
            [0, 0, 1, 1],
            [1, 1, 1, 1]
        ]
    start = time.time()
    f = ImplicationFrame(2, bound=2, example=matrix1)
    end = time.time()
    print(f"Time to construct f: {end - start:.6f} seconds")

    print(f)

    # group candidate implications by identical RSRs
    unique_rsrs = defaultdict(list)
    for ci, rsr in f.RSRs.items():
        rsr_key = tuple(sorted(rsr))
        unique_rsrs[rsr_key].append(ci)

    one = f.back_translate_implication("a,a |~ b")
    two = f.back_translate_implication("a,b |~ a,a")
    rsr = f.RSR((one,two))
    print(f.pretty_print_rsr(rsr))

    # test factoring for each unique RSR
    print(f.factor(rsr))
    # test symjunction behavior
    role_one = f.role((one,))
    role_two = f.role((two,))
    symj = f.symjunction([role_one, role_two])
    direct_role = f.role((one, two))
    assert symj == direct_role, f"symjunction mismatch: {symj} != {direct_role}"
    # commutativity check
    symj_rev = f.symjunction([role_two, role_one])
    assert symj_rev == symj, f"symjunction not commutative: {symj_rev} != {symj}"
    print("symjunction tests passed")

if __name__ == "__main__":
    main()