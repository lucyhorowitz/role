from ImplFrame import *

if __name__ == "__main__":

    # a two-bearer example where a represents a dollar and b represents a chocolate bar, costing $1
    chocolate = ["a|~", "a|~b", "b|~", "aa|~", "aa|~a","aa|~b", "aa|~ab", "aa|~bb", "ab|~", "ab|~a",
                "ab|~b", "ab|~bb", "bb|~", "bb|~b", "aab|~","aab|~a","aab|~b","aab|~aa","aab|~ab",
                "aab|~bb", "aab|~abb", "abb|~", "abb|~a","abb|~b","abb|~ab", "abb|~bb", "aabb|~",
                "aabb|~a","aabb|~b","aabb|~aa","aabb|~ab","aabb|~bb","aabb|~aab","aabb|~abb"]
    
    f1 = ImplicationFrame(2, chocolate, False, True)
    print(f"Chocolate frame:\n{f1}")
    RSR = f1.RSR("aa|~bb")
    print(f"RSR(aa |~ bb): {RSR}")
    print(f"Translates to: {[cindex_to_implication(a,2) for a in RSR[0]]} with {cindex_to_implication(RSR[1].pop(),2)} plus reflexive implications")
    print()
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


    
