The implementation consists of approximately 13'000 lines of code, formalizing finite automata, regular expressions and (strictly) regular grammars, analyzing their properties, and proving significant results.
A central result of this work is the formal verification of the equivalence in expressive power between several concepts:
- nondeterministic finite automata (NFAs) and deterministic finite automata (DFAs), demonstrating that for every NFA there exists a DFA accepting the same language.
- NFAs and NFA-multis (NFAs with multiple initial states), demonstrating that for every NFA there exists a NFA-multi accepting the same language.
- NFAs and Epsilon-NFAs, demonstrating that for every NFA there exists a Epsilon-NFA accepting the same language.
- NFAs and regular expressions, demonstrating that for every NFA there exists a RE generating the same language.
- NFAs and right regular grammars, demonstrating that for every NFA there exists a RRG generating the same language.
- NFAs and left regular grammars, demonstrating that for every NFA there exists a LRG generating the same language.

Furthermore, it is formally proven that the class of regular languages is closed under the operations of intersection, union, complementation, reversal, concatenation and kleene-star-closure.
In addition, Brzozowksi's algorithm for DFA minimization is implemented and verified, i.e. for every NFA there exists an unique (up to renaming its states) DFA accepting the same language.
Last but not least, the pumping lemma for regular languages is implemented. The code and theorems are far from optimally implemented nor efficiently automated.

In "automaton_examples.thy" there are several examples demonstrating the code, building on all the theories before. Download all theories, open automaton_examples.thy and enjoy!
