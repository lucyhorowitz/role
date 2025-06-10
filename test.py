# A file that demonstrates current capabilities of ImplFrame.py

from ImplFrame import *

if __name__ == "__main__":
    implications = ["a |~ b", "b |~ a", "a |~ ", "aa |~ "]

    f1 = ImplicationFrame(2, implications)
    print("A reflexive, containment implication frame from the implications:")
    print(f1)


    print("A nonreflexive, noncontainment implication frame from the implications:")
    f2 = ImplicationFrame(2, implications, False, False)
    print(f2)