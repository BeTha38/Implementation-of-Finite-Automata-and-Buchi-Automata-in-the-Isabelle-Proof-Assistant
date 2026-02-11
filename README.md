This project contains approximately 17'000 lines of Isabelle/HOL code formalizing finite automata, regular expressions, and (strictly) regular grammars, and Büchi automata and omega regular expressions.
It analyzes their theoretical properties and formally proves a number of classic results from automata theory.

A central outcome of this development is the formal verification of the equivalence in expressive power between several formalisms. In particular, it is shown that for every NFA there exists an equivalent automaton/epxression/grammar accepting the same language:

* Deterministic finite automata (DFAs)
* NFAs with multiple initial states (NFA-multi)
* Epsilon-NFAs
* Regular expressions (REs)
* Right-regular grammars (RRGs)
* Left-regular grammars (LRGs)

Furthermore, it is formally proved that the class of regular languages is closed under:

* intersection
* union
* complementation
* relative complementation
* reversal
* concatenation
* Kleene star
* all finite languages are regular

In addition, Brzozowski's algorithm for DFA minimization is implemented and verified: for every NFA there exists a unique (up to renaming of states) minimal DFA accepting the same language.

Finally, the pumping lemma for regular languages is formalized.



For Büchi automata it is shown, that NBAs have the same expressive power as omega regular expressions. For DBAs there is a simple complementation algorithm.

Furthermore, it is formally proven that the class of omega regular languages is closed under:

* intersection
* union
* concatenation of a regular and an omega regular language
* omega power



The code and proofs are not optimized nor heavily automated; the focus of the project is correctness and transparency rather than efficiency.

The file automaton\_examples.thy contains a number of example automata and demonstrations. To explore the project:

1. Download all theory files
2. Open automaton\_examples.thy in Isabelle
3. Enjoy experimenting with the provided constructions and proofs
