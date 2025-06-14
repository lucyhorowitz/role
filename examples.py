from ImplFrame import *

if __name__ == "__main__":

    # a two-bearer example where a represents a dollar and b represents a chocolate bar, costing $1
    chocolate = ["a|~", "a|~b", "b|~", "aa|~", "aa|~a","aa|~b", "aa|~ab", "aa|~bb", "ab|~", "ab|~a",
                "ab|~b", "ab|~bb", "bb|~", "bb|~b", "aab|~","aab|~a","aab|~b","aab|~aa","aab|~ab",
                "aab|~bb", "aab|~abb", "abb|~", "abb|~a","abb|~b","abb|~ab", "abb|~bb", "aabb|~",
                "aabb|~a","aabb|~b","aabb|~aa","aabb|~ab","aabb|~bb","aabb|~aab","aabb|~abb"]
    
    import itertools

    f1 = ImplicationFrame(2, chocolate, False, True)
    print(f"Chocolate frame:\n{f1}")

    # ---- generate all candidate implication pairs up to (aab |~ aab) ----
    max_a, max_b = 2, 2  # counts in "aab"
    strings = ['']  # include the empty string for sides like "|~a"
    for a_cnt in range(max_a + 1):
        for b_cnt in range(max_b + 1):
            if a_cnt == b_cnt == 0:
                continue
            strings.append('a' * a_cnt + 'b' * b_cnt)

    cand_up_to = [f"{lhs}|~{rhs}" for lhs in strings for rhs in strings]
    cand_pairs = list(itertools.combinations(cand_up_to, 2))  # unordered pairs

    print(f"\nall {len(cand_pairs)} pairs of candidate implications up to (aabb|~aabb):")
    count = 0
    for lhs, rhs in cand_pairs:
        RSR1 = f1.RSR(lhs)
        RSR2 = f1.RSR(rhs)
        adj = f1.adjunction(RSR1, RSR2)
        
        if adj[0] or adj[1]:
            
            count +=1
            print(f"{lhs} , {rhs} has adjunction {[cindex_to_implication(i,2) for i in adj[0]],[cindex_to_implication(i,2) for i in adj[1]]}")


    print(f"There are {count} nontrivial adjunctions up to {len(cand_pairs)}")
    # ---------------------------------------------------------------------

    

    RSR = f1.RSR("aa|~bb")

    
    
    print(f"RSR(aa |~ bb): {RSR}")
    print(f"Translates to: {[cindex_to_implication(a,2) for a in RSR[0]]} with {[cindex_to_implication(thing,2) for thing in RSR[1]]} plus reflexive implications")
    print()
    RSR2 = f1.RSR(RSR)
    print(f"RSR^2(aa |~ bb): {RSR2}")
    print(f"Translates to: {[cindex_to_implication(a,2) for a in RSR2[0]]} with {[cindex_to_implication(thing,2) for thing in RSR2[1]]} plus reflexive implications")

    

    # a one-bearer example with a nontrivial adjunction
    one_bearer = ["|~a", "|~aa", "a|~", "aa|~a", "aaa|~", "aaa|~aa"]
    f2 = ImplicationFrame(1, one_bearer, False, True)
    print(f"One-bearer frame:\n{f2}")
    one = f2.RSR("|~ a")
    print(f"RSR(|~ a): {one}")
    print(f"Translates to: {[cindex_to_implication(a,1) for a in one[0]]} with {[cindex_to_implication(a,1) for a in one[1]]} plus reflexive implications")
    two = f2.RSR("a |~ aa")
    print(f"RSR(a |~ aa): {two}")
    print(f"Translates to: {[cindex_to_implication(a,1) for a in two[0]]} with {[cindex_to_implication(a,1) for a in two[1]]} plus reflexive implications")
    ot = f2.otimes(one, two)
    print(f"RSR(|~ a) x RSR(a |~ aa): {ot}")
    print(f"Translates to: {[cindex_to_implication(a,1) for a in ot[0]]}")
    rsr_prime = f2.RSR(ot)
    print(f"RSR(RSR(|~ a) x RSR(a |~ aa)): {rsr_prime}")
    print(f"Translates to: {[cindex_to_implication(a,1) for a in rsr_prime[0]]}")


    
