The implementation consists of approximately 11'700 lines of code, formalizing finite automata, regular expressions and (strictly) regular grammars, analyzing their properties, and proving significant results.
A central result of this work is the formal verification of the equivalence in expressive power between several concepts:
- nondeterministic finite automata (NFAs) and deterministic finite automata (DFAs), demonstrating that for every NFA there exists a DFA accepting the same language
- NFAs and NFA-multis (NFAs with multiple initial states), ''
- NFAs and Epsilon-NFAs, ''
- NFAs and regular expressions, ''
- NFAs and right regular grammars, ''
- NFAs and left regular grammars.
Furthermore, it is formally proven that the class of languages recognized by finite automata is closed under the operations of intersection, union, complementation, reversal, concatenation and kleene-star-closure.
In addition, Brzozowksi's algorithm for DFA minimization is implemented and verified, i.e. for every NFA there exists an unique (up to renaming its states) DFA accepting the same language.

In "automaton_examples.thy" there are several examples demonstrating the code, building on all the theories before. Download all theories, open automaton_examples.thy and enjoy!
