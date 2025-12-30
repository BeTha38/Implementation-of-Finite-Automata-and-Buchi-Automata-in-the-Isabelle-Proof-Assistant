This project contains approximately 13,000 lines of Isabelle/HOL code formalizing finite automata, regular expressions, and (strictly) regular grammars.
It analyzes their theoretical properties and formally proves a number of classic results from automata theory.

A central outcome of this development is the formal verification of the equivalence in expressive power between several formalisms. In particular, it is shown that for every NFA there exists an equivalent automaton (or epxression/grammar) accepting the same language:
- Deterministic finite automata (DFAs)
- NFAs with multiple initial states (NFA-multi)
- Epsilon-NFAs
- Regular expressions (REs)
- Right-regular grammars (RRGs)
- Left-regular grammars (LRGs)

Furthermore, it is formally proved that the class of regular languages is closed under:
- intersection
- union
- complementation
- relative complementation
- reversal
- concatenation
- Kleene star
- all finite languages are regular

In addition, Brzozowski’s algorithm for DFA minimization is implemented and verified: for every NFA there exists a unique (up to renaming of states) minimal DFA accepting the same language.

Finally, the pumping lemma for regular languages is formalized.

The code and proofs are not optimized nor heavily automated; the focus of the project is correctness and transparency rather than efficiency.

The file automaton_examples.thy contains a number of example automata and demonstrations. To explore the project:
1. Download all theory files
2. Open automaton_examples.thy in Isabelle
3. Enjoy experimenting with the provided constructions and proofs
